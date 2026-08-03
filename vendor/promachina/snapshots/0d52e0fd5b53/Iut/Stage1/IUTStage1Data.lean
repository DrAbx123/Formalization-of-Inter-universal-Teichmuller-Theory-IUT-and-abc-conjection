/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTSourceScaffold

/-!
Named pre-ledger data for future IUT-specific Stage 1 constructions.

This module records the source-specific ingredients that should eventually feed
a `SourceObligationLedger`. It deliberately stops before constructing that
ledger, so missing obligations remain visible.
-/

namespace Iut
namespace Stage1

open RealLineCopy

/-- Inert identifier for the Stage 1 input data, e.g. a base prime-strip package. -/
structure Stage1InputId where
  label : String

/-- Inert identifier for the multiradial output supplied by the Stage 1 algorithm. -/
structure MultiradialOutputId where
  label : String

/-- Inert identifier for the final charted log-volume comparison package. -/
structure LogVolumeComparisonId where
  label : String

/--
Pre-ledger Stage 1 data for a future IUT-specific construction.

The record separates qualitative data, multiradial output labels, charted
q/Theta log-volume data, selected output data, and membership data. It does not
claim that the remaining source obligations needed for a
`SourceObligationLedger` have been discharged.
-/
structure IUTStage1PreLedgerData (source target : Copy) (index : Type u) where
  input : Stage1InputId
  multiradialOutput : MultiradialOutputId
  logVolumeComparison : LogVolumeComparisonId
  output : AlgorithmicOutput source target index
  measure : RegionMeasure target
  thetaSigned : Real
  qSigned : Real
  normalization : Prop
  certificate : QualitativeData.StructuredCertificate output.family
  chartedContainer : output.ChartedCommonContainerData measure thetaSigned
  qValue : output.ChartedQValueData measure chartedContainer.chart qSigned
  thetaBound : output.ChartedThetaBoundData measure chartedContainer.chart thetaSigned
  chosenOutput : output.ChosenOutputData
  targetVolume :
    output.ChartedTargetVolumeData measure chartedContainer.chart chosenOutput.choice
  membership :
    output.ChartedMembershipData measure chartedContainer.chart
      qValue chosenOutput targetVolume

namespace IUTStage1PreLedgerData

variable {source target : Copy} {index : Type u}
variable {newIndex : Type v}

set_option linter.style.longLine false in
/--
Pull a pre-ledger back along a choice map, provided the chosen output has a
specified lift.

The common-container bridge for the pulled-back output is obtained by pulling
back the already constructed common-target bound from the original pre-ledger.
Thus no new common-container or hull/determinant assumption is introduced; the
only extra datum is the generated choice that maps to the old selected output.
-/
def reindex
    (data : IUTStage1PreLedgerData source target index)
    (f : newIndex -> index)
    (chosen : newIndex)
    (hchosen : f chosen = data.chosenOutput.choice) :
    IUTStage1PreLedgerData source target newIndex :=
  let output' := data.output.reindex f
  let certificate' := data.certificate.reindex f
  let originalCommonBound := data.chartedContainer.apply data.certificate
  let pulledCommonBridge :
      output'.StructuredCommonTargetBoundBridge data.measure data.thetaSigned :=
    { build := fun _ =>
        { common := originalCommonBound.common,
          contains_each := by
            intro choice
            exact originalCommonBound.contains_each (f choice),
          volume_bound := originalCommonBound.volume_bound } }
  let chosenOutput' : output'.ChosenOutputData :=
    { choice := chosen,
      comparison := data.chosenOutput.comparison,
      comparison_eq := by
        calc
          data.chosenOutput.comparison =
              data.output.comparison data.chosenOutput.choice :=
            data.chosenOutput.comparison_eq
          _ = data.output.comparison (f chosen) := by
            rw [hchosen] }
  let targetVolume' :
      output'.ChartedTargetVolumeData data.measure
        { chart := data.chartedContainer.chart.chart,
          qToTarget := data.chartedContainer.chart.qToTarget,
          thetaToTarget := data.chartedContainer.chart.thetaToTarget,
          theta_trivial := data.chartedContainer.chart.theta_trivial }
        chosenOutput'.choice :=
    { targetSigned := data.targetVolume.targetSigned,
      targetSigned_eq := by
        calc
          data.targetVolume.targetSigned =
              RegionMeasure.targetVolume data.measure
                (data.output.comparison data.chosenOutput.choice) :=
            data.targetVolume.targetSigned_eq
          _ = RegionMeasure.targetVolume data.measure
                (data.output.comparison (f chosen)) := by
            rw [hchosen] }
  { input := data.input,
    multiradialOutput := data.multiradialOutput,
    logVolumeComparison := data.logVolumeComparison,
    output := output',
    measure := data.measure,
    thetaSigned := data.thetaSigned,
    qSigned := data.qSigned,
    normalization := data.normalization,
    certificate := certificate',
    chartedContainer :=
      { commonContainer :=
          { container := data.chartedContainer.commonContainer.container,
            context := certificate'.she.sharedContext,
            hddShe :=
              { sheArrow :=
                  { arrow := data.chartedContainer.commonContainer.hddShe.sheArrow.arrow,
                    datum := certificate'.she },
                hdd :=
                  { descent := data.chartedContainer.commonContainer.hddShe.hdd.descent,
                    hullDetBridge :=
                      { operation :=
                          data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge.operation,
                        bridge := pulledCommonBridge } } },
            she_context_matches := rfl },
        chart :=
          { chart := data.chartedContainer.chart.chart,
            qToTarget := data.chartedContainer.chart.qToTarget,
            thetaToTarget := data.chartedContainer.chart.thetaToTarget,
            theta_trivial := data.chartedContainer.chart.theta_trivial } },
    qValue :=
      { qPoint := data.qValue.qPoint,
        qSigned_eq := data.qValue.qSigned_eq },
    thetaBound :=
      { thetaPoint := data.thetaBound.thetaPoint,
        thetaSigned_eq := data.thetaBound.thetaSigned_eq },
    chosenOutput := chosenOutput',
    targetVolume := targetVolume',
    membership :=
      { holds := data.membership.holds,
        q_chart_transport_eq := data.membership.q_chart_transport_eq,
        volume_control := data.membership.volume_control } }

def hasStructuredIPL (data : IUTStage1PreLedgerData source target index) :
    QualitativeData.HasStructuredIPL data.output.family :=
  data.certificate.hasStructuredIPL

def hasStructuredSHE (data : IUTStage1PreLedgerData source target index) :
    QualitativeData.HasStructuredSHE data.output.family :=
  data.certificate.hasStructuredSHE

def hasStructuredAPT (data : IUTStage1PreLedgerData source target index) :
    QualitativeData.HasStructuredAPT data.output.family :=
  data.certificate.hasStructuredAPT

theorem thetaChartTrivial (data : IUTStage1PreLedgerData source target index) :
    Transport.TrivialMonodromy data.chartedContainer.chart.thetaToTarget :=
  data.chartedContainer.thetaTrivial

theorem qSigned_eq_chartedQ (data : IUTStage1PreLedgerData source target index) :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord = data.qSigned :=
  data.qValue.qSigned_eq

theorem thetaSigned_eq_chartedTheta
    (data : IUTStage1PreLedgerData source target index) :
    (Transport.map data.chartedContainer.chart.thetaToTarget
      data.thetaBound.thetaPoint).coord = data.thetaSigned :=
  data.thetaBound.thetaSigned_eq

theorem chosenComparisonHoldsQ
    (data : IUTStage1PreLedgerData source target index) :
    data.chosenOutput.comparison.Holds data.qValue.qPoint :=
  data.membership.holds

theorem qSigned_le_targetSigned
    (data : IUTStage1PreLedgerData source target index) :
    data.qSigned <= data.targetVolume.targetSigned :=
  data.membership.q_le_target

theorem targetSigned_eq_choiceTargetVolume
    (data : IUTStage1PreLedgerData source target index) :
    data.targetVolume.targetSigned =
      RegionMeasure.targetVolume data.measure
        (data.output.comparison data.chosenOutput.choice) :=
  data.targetVolume.targetSigned_eq

theorem choiceTargetVolume_le_thetaSigned
    (data : IUTStage1PreLedgerData source target index) :
    RegionMeasure.targetVolume data.measure
        (data.output.comparison data.chosenOutput.choice) <=
      data.thetaSigned :=
  data.chartedContainer.choice_targetVolume_le
    data.certificate data.chosenOutput.choice

theorem targetSigned_le_thetaSigned
    (data : IUTStage1PreLedgerData source target index) :
    data.targetVolume.targetSigned <= data.thetaSigned := by
  rw [data.targetSigned_eq_choiceTargetVolume]
  exact data.choiceTargetVolume_le_thetaSigned

/--
Pre-ledger comparison chain stated with charted q and Theta endpoints.

This is the local source of the later charted q-to-Theta comparison. The
middle term is still the measured target volume of the chosen output.
-/
structure ChartedComparisonChain
    (data : IUTStage1PreLedgerData source target index) : Prop where
  q_charted :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord = data.qSigned
  theta_charted :
    (Transport.map data.chartedContainer.chart.thetaToTarget
      data.thetaBound.thetaPoint).coord = data.thetaSigned
  q_chart_transport_eq :
    data.chartedContainer.chart.qToTarget =
      data.chosenOutput.comparison.transport
  membership_volume_control :
    data.chosenOutput.comparison.MembershipControlsTargetVolume data.measure
  target_signed_eq_choice_volume :
    data.targetVolume.targetSigned =
      RegionMeasure.targetVolume data.measure
        (data.output.comparison data.chosenOutput.choice)
  choice_target_volume_le_theta :
    RegionMeasure.targetVolume data.measure
        (data.output.comparison data.chosenOutput.choice) <=
      data.thetaSigned
  q_charted_le_target :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord <= data.targetVolume.targetSigned
  target_le_theta_charted :
    data.targetVolume.targetSigned <=
      (Transport.map data.chartedContainer.chart.thetaToTarget
        data.thetaBound.thetaPoint).coord
  charted_q_le_charted_theta :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord <=
      (Transport.map data.chartedContainer.chart.thetaToTarget
        data.thetaBound.thetaPoint).coord

theorem chartedComparisonChain
    (data : IUTStage1PreLedgerData source target index) :
    data.ChartedComparisonChain :=
  { q_charted := data.qSigned_eq_chartedQ,
    theta_charted := data.thetaSigned_eq_chartedTheta,
    q_chart_transport_eq := data.membership.q_chart_transport_eq,
    membership_volume_control := data.membership.volume_control,
    target_signed_eq_choice_volume := data.targetSigned_eq_choiceTargetVolume,
    choice_target_volume_le_theta := data.choiceTargetVolume_le_thetaSigned,
    q_charted_le_target := by
      rw [data.qSigned_eq_chartedQ]
      exact data.qSigned_le_targetSigned,
    target_le_theta_charted := by
      rw [data.thetaSigned_eq_chartedTheta]
      exact data.targetSigned_le_thetaSigned,
    charted_q_le_charted_theta := by
      rw [data.qSigned_eq_chartedQ, data.thetaSigned_eq_chartedTheta]
      exact le_trans data.qSigned_le_targetSigned data.targetSigned_le_thetaSigned }

namespace ChartedComparisonChain

variable {data : IUTStage1PreLedgerData source target index}

theorem qCharted
    (chain : data.ChartedComparisonChain) :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord = data.qSigned :=
  chain.q_charted

theorem thetaCharted
    (chain : data.ChartedComparisonChain) :
    (Transport.map data.chartedContainer.chart.thetaToTarget
      data.thetaBound.thetaPoint).coord = data.thetaSigned :=
  chain.theta_charted

theorem qChartTransport_eq_comparisonTransport
    (chain : data.ChartedComparisonChain) :
    data.chartedContainer.chart.qToTarget =
      data.chosenOutput.comparison.transport :=
  chain.q_chart_transport_eq

theorem membershipVolumeControl
    (chain : data.ChartedComparisonChain) :
    data.chosenOutput.comparison.MembershipControlsTargetVolume data.measure :=
  chain.membership_volume_control

theorem targetSigned_eq_choiceTargetVolume
    (chain : data.ChartedComparisonChain) :
    data.targetVolume.targetSigned =
      RegionMeasure.targetVolume data.measure
        (data.output.comparison data.chosenOutput.choice) :=
  chain.target_signed_eq_choice_volume

theorem choiceTargetVolume_le_thetaSigned
    (chain : data.ChartedComparisonChain) :
    RegionMeasure.targetVolume data.measure
        (data.output.comparison data.chosenOutput.choice) <=
      data.thetaSigned :=
  chain.choice_target_volume_le_theta

theorem qCharted_le_targetSigned
    (chain : data.ChartedComparisonChain) :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord <= data.targetVolume.targetSigned :=
  chain.q_charted_le_target

theorem targetSigned_le_thetaCharted
    (chain : data.ChartedComparisonChain) :
    data.targetVolume.targetSigned <=
      (Transport.map data.chartedContainer.chart.thetaToTarget
        data.thetaBound.thetaPoint).coord :=
  chain.target_le_theta_charted

theorem chartedQ_le_chartedTheta
    (chain : data.ChartedComparisonChain) :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord <=
      (Transport.map data.chartedContainer.chart.thetaToTarget
        data.thetaBound.thetaPoint).coord :=
  chain.charted_q_le_charted_theta

end ChartedComparisonChain

/--
Source-side inputs that determine the signed q-to-Theta comparison payload.

This record deliberately stops before q-positivity and source normalization.
Those are promotion obligations, not chart/membership data.
-/
structure ComparisonPayloadInputs
    (data : IUTStage1PreLedgerData source target index) where
  theta_chart_trivial :
    Transport.TrivialMonodromy data.chartedContainer.chart.thetaToTarget
  q_charted :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord = data.qSigned
  theta_charted :
    (Transport.map data.chartedContainer.chart.thetaToTarget
      data.thetaBound.thetaPoint).coord = data.thetaSigned
  chosen_holds :
    data.chosenOutput.comparison.Holds data.qValue.qPoint
  q_le_target :
    data.qSigned <= data.targetVolume.targetSigned
  target_le_theta :
    data.targetVolume.targetSigned <= data.thetaSigned

theorem comparisonPayloadInputs
    (data : IUTStage1PreLedgerData source target index) :
    data.ComparisonPayloadInputs :=
  { theta_chart_trivial := data.thetaChartTrivial,
    q_charted := data.qSigned_eq_chartedQ,
    theta_charted := data.thetaSigned_eq_chartedTheta,
    chosen_holds := data.chosenComparisonHoldsQ,
    q_le_target := data.qSigned_le_targetSigned,
    target_le_theta := data.targetSigned_le_thetaSigned }

namespace ComparisonPayloadInputs

variable {data : IUTStage1PreLedgerData source target index}

theorem thetaChartTrivial
    (inputs : data.ComparisonPayloadInputs) :
    Transport.TrivialMonodromy data.chartedContainer.chart.thetaToTarget :=
  inputs.theta_chart_trivial

theorem qCharted
    (inputs : data.ComparisonPayloadInputs) :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord = data.qSigned :=
  inputs.q_charted

theorem thetaCharted
    (inputs : data.ComparisonPayloadInputs) :
    (Transport.map data.chartedContainer.chart.thetaToTarget
      data.thetaBound.thetaPoint).coord = data.thetaSigned :=
  inputs.theta_charted

theorem chosenHolds
    (inputs : data.ComparisonPayloadInputs) :
    data.chosenOutput.comparison.Holds data.qValue.qPoint :=
  inputs.chosen_holds

theorem qSignedLeTargetSigned
    (inputs : data.ComparisonPayloadInputs) :
    data.qSigned <= data.targetVolume.targetSigned :=
  inputs.q_le_target

theorem targetSignedLeThetaSigned
    (inputs : data.ComparisonPayloadInputs) :
    data.targetVolume.targetSigned <= data.thetaSigned :=
  inputs.target_le_theta

theorem qSignedLeThetaSigned
    (inputs : data.ComparisonPayloadInputs) :
    data.qSigned <= data.thetaSigned :=
  le_trans inputs.qSignedLeTargetSigned inputs.targetSignedLeThetaSigned

def comparisonData
    (inputs : data.ComparisonPayloadInputs)
    (hq_positive : 0 < -data.qSigned) :
    Corollary312ComparisonData :=
  { thetaSigned := data.thetaSigned,
    qSigned := data.qSigned,
    q_positive := hq_positive,
    qSigned_le_thetaSigned := inputs.qSignedLeThetaSigned }

theorem comparisonData_thetaSigned
    (inputs : data.ComparisonPayloadInputs)
    (hq_positive : 0 < -data.qSigned) :
    (inputs.comparisonData hq_positive).thetaSigned = data.thetaSigned :=
  rfl

theorem comparisonData_qSigned
    (inputs : data.ComparisonPayloadInputs)
    (hq_positive : 0 < -data.qSigned) :
    (inputs.comparisonData hq_positive).qSigned = data.qSigned :=
  rfl

theorem comparisonData_corollary312
    (inputs : data.ComparisonPayloadInputs)
    (hq_positive : 0 < -data.qSigned) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta data.thetaSigned)
      (signedPilotLogVolume PilotSide.q data.qSigned) :=
  (inputs.comparisonData hq_positive).corollary312

end ComparisonPayloadInputs

/--
Constructed qualitative certificate for the pre-ledger family.

This pins the certificate used by the Stage 1 ledger to explicit source-shaped
IPL, SHE, and APT constructions: input-prime-strip links, a Hodge-theater
transport context with a forbidden-identification guard, and a permitted APT
transport arrow.
-/
structure ConstructedQualitativeCertificateData
    (data : IUTStage1PreLedgerData source target index) where
  iplConstruction :
    QualitativeData.InputPrimeStripLinkConstruction data.output.family
  sheTransportContext :
    QualitativeData.StructuredSHETransportContext data.output.family
  aptConstruction :
    QualitativeData.AlgorithmicParallelTransportConstruction data.output.family
  certificate_eq :
    data.certificate =
      QualitativeData.StructuredCertificate.ofConstructedIPLSHEAPT
        iplConstruction sheTransportContext aptConstruction

namespace ConstructedQualitativeCertificateData

variable {data : IUTStage1PreLedgerData source target index}

def constructedCertificate
    (sourceData : ConstructedQualitativeCertificateData data) :
    QualitativeData.StructuredCertificate data.output.family :=
  QualitativeData.StructuredCertificate.ofConstructedIPLSHEAPT
    sourceData.iplConstruction sourceData.sheTransportContext
    sourceData.aptConstruction

theorem certificate_eq_constructed
    (sourceData : ConstructedQualitativeCertificateData data) :
    data.certificate = sourceData.constructedCertificate :=
  sourceData.certificate_eq

theorem hasStructuredIPL
    (sourceData : ConstructedQualitativeCertificateData data) :
    QualitativeData.HasStructuredIPL data.output.family :=
  sourceData.constructedCertificate.hasStructuredIPL

theorem hasStructuredSHE
    (sourceData : ConstructedQualitativeCertificateData data) :
    QualitativeData.HasStructuredSHE data.output.family :=
  sourceData.constructedCertificate.hasStructuredSHE

theorem hasStructuredAPT
    (sourceData : ConstructedQualitativeCertificateData data) :
    QualitativeData.HasStructuredAPT data.output.family :=
  sourceData.constructedCertificate.hasStructuredAPT

theorem aptDatum_eq_constructed
    (sourceData : ConstructedQualitativeCertificateData data) :
    data.certificate.apt = sourceData.aptConstruction.toAPTDatum := by
  rw [sourceData.certificate_eq_constructed]
  rfl

def QualitativeTransportAudit
    (sourceData : ConstructedQualitativeCertificateData data) : Prop :=
  QualitativeData.HasStructuredIPL data.output.family ∧
    QualitativeData.HasStructuredSHE data.output.family ∧
    QualitativeData.HasStructuredAPT data.output.family ∧
    (∀ mechanism : QualitativeData.TransportMechanismId,
      ¬ sourceData.sheTransportContext.transportSystem.Allows
        sourceData.sheTransportContext.baseContext.domainStructure.theater
        sourceData.sheTransportContext.baseContext.codomainStructure.theater
        mechanism) ∧
    ¬ sourceData.aptConstruction.transportSystem.forbiddenIdentification
      sourceData.aptConstruction.arrow.source
      sourceData.aptConstruction.arrow.target

theorem qualitativeTransportAudit
    (sourceData : ConstructedQualitativeCertificateData data) :
    sourceData.QualitativeTransportAudit :=
  ⟨sourceData.hasStructuredIPL,
    sourceData.hasStructuredSHE,
    sourceData.hasStructuredAPT,
    sourceData.sheTransportContext.noAllowedDomainToCodomainWithMechanism,
    sourceData.aptConstruction.permitted_not_forbidden⟩

def APTTransportAudit
    (sourceData : ConstructedQualitativeCertificateData data) : Prop :=
  data.certificate.apt = sourceData.aptConstruction.toAPTDatum ∧
    data.certificate.apt.arrow =
      sourceData.aptConstruction.arrow ∧
    data.certificate.apt.mechanism =
      sourceData.aptConstruction.arrow.mechanism ∧
    data.certificate.apt.outputFamily =
      sourceData.aptConstruction.outputFamily ∧
    data.certificate.apt.outputFamily = data.output.family ∧
    data.certificate.apt.TransportQuotientEndpoint ∧
    sourceData.aptConstruction.transportSystem.allowed
      sourceData.aptConstruction.arrow ∧
    ¬ sourceData.aptConstruction.transportSystem.forbiddenIdentification
      sourceData.aptConstruction.arrow.source
      sourceData.aptConstruction.arrow.target ∧
    QualitativeData.AlgorithmicParallelTransportConstruction.APTTransportQuotientAudit
      sourceData.aptConstruction

theorem aptTransportAudit
    (sourceData : ConstructedQualitativeCertificateData data) :
    sourceData.APTTransportAudit := by
  refine ⟨sourceData.aptDatum_eq_constructed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceData.aptDatum_eq_constructed]
    exact sourceData.aptConstruction.toAPTDatum_arrow_eq
  · rw [sourceData.aptDatum_eq_constructed]
    exact sourceData.aptConstruction.toAPTDatum_mechanism_eq_arrow
  · rw [sourceData.aptDatum_eq_constructed]
    exact sourceData.aptConstruction.toAPTDatum_outputFamily_eq
  · rw [sourceData.aptDatum_eq_constructed]
    exact sourceData.aptConstruction.toAPTDatum_output_eq_family
  · rw [sourceData.aptDatum_eq_constructed]
    exact sourceData.aptConstruction.toAPTDatum_transportQuotientEndpoint
  · exact sourceData.aptConstruction.permitted
  · exact sourceData.aptConstruction.permitted_not_forbidden
  · exact sourceData.aptConstruction.aptTransportQuotientAudit

end ConstructedQualitativeCertificateData

/-- Local audit of pre-ledger data, before the remaining ledger obligations. -/
structure Audit (data : IUTStage1PreLedgerData source target index) : Prop where
  has_structured_ipl : QualitativeData.HasStructuredIPL data.output.family
  has_structured_she : QualitativeData.HasStructuredSHE data.output.family
  has_structured_apt : QualitativeData.HasStructuredAPT data.output.family
  theta_chart_trivial :
    Transport.TrivialMonodromy data.chartedContainer.chart.thetaToTarget
  q_charted :
    (Transport.map data.chartedContainer.chart.qToTarget
      data.qValue.qPoint).coord = data.qSigned
  theta_charted :
    (Transport.map data.chartedContainer.chart.thetaToTarget
      data.thetaBound.thetaPoint).coord = data.thetaSigned
  chosen_holds :
    data.chosenOutput.comparison.Holds data.qValue.qPoint
  q_le_target :
    data.qSigned <= data.targetVolume.targetSigned
  target_le_theta :
    data.targetVolume.targetSigned <= data.thetaSigned

theorem audit (data : IUTStage1PreLedgerData source target index) :
    Audit data :=
  { has_structured_ipl := data.hasStructuredIPL,
    has_structured_she := data.hasStructuredSHE,
    has_structured_apt := data.hasStructuredAPT,
    theta_chart_trivial := data.thetaChartTrivial,
    q_charted := data.qSigned_eq_chartedQ,
    theta_charted := data.thetaSigned_eq_chartedTheta,
    chosen_holds := data.chosenComparisonHoldsQ,
    q_le_target := data.qSigned_le_targetSigned,
    target_le_theta := data.targetSigned_le_thetaSigned }

def auditOfConstructedQualitativeCertificate
    (data : IUTStage1PreLedgerData source target index)
    (sourceData : ConstructedQualitativeCertificateData data) :
    Audit data :=
  { has_structured_ipl := sourceData.hasStructuredIPL,
    has_structured_she := sourceData.hasStructuredSHE,
    has_structured_apt := sourceData.hasStructuredAPT,
    theta_chart_trivial := data.thetaChartTrivial,
    q_charted := data.qSigned_eq_chartedQ,
    theta_charted := data.thetaSigned_eq_chartedTheta,
    chosen_holds := data.chosenComparisonHoldsQ,
    q_le_target := data.qSigned_le_targetSigned,
    target_le_theta := data.targetSigned_le_thetaSigned }

theorem auditOfConstructedQualitativeCertificate_qualitativeTransportAudit
    {data : IUTStage1PreLedgerData source target index}
    (sourceData : ConstructedQualitativeCertificateData data) :
    sourceData.QualitativeTransportAudit :=
  sourceData.qualitativeTransportAudit

theorem auditOfConstructedQualitativeCertificate_eq_audit
    (data : IUTStage1PreLedgerData source target index)
    (sourceData : ConstructedQualitativeCertificateData data) :
    auditOfConstructedQualitativeCertificate data sourceData = audit data :=
  Subsingleton.elim _ _

namespace Audit

variable {data : IUTStage1PreLedgerData source target index}

def comparisonPayloadInputs
    (audit : Audit data) :
    data.ComparisonPayloadInputs :=
  { theta_chart_trivial := audit.theta_chart_trivial,
    q_charted := audit.q_charted,
    theta_charted := audit.theta_charted,
    chosen_holds := audit.chosen_holds,
    q_le_target := audit.q_le_target,
    target_le_theta := audit.target_le_theta }

theorem comparisonPayloadInputs_eq_data
    (audit : Audit data) :
    audit.comparisonPayloadInputs = data.comparisonPayloadInputs :=
  Subsingleton.elim _ _

theorem comparisonPayloadInputs_qSignedLeThetaSigned
    (audit : Audit data) :
    audit.comparisonPayloadInputs.qSignedLeThetaSigned =
      data.comparisonPayloadInputs.qSignedLeThetaSigned :=
  Subsingleton.elim _ _

theorem qSignedLeThetaSigned
    (audit : Audit data) :
    data.qSigned <= data.thetaSigned :=
  audit.comparisonPayloadInputs.qSignedLeThetaSigned

end Audit

theorem auditOfConstructedQualitativeCertificate_qSignedLeThetaSigned
    {data : IUTStage1PreLedgerData source target index}
    (sourceData : ConstructedQualitativeCertificateData data) :
    data.qSigned <= data.thetaSigned :=
  (auditOfConstructedQualitativeCertificate data sourceData).qSignedLeThetaSigned

/--
Constructed common-container provenance for a pre-ledger.

The qualitative certificate already pins the certificate's SHE datum to a
structured Hodge-theater transport context. This record additionally requires
the pre-ledger common container's SHE arrow and shared context to be aligned
with that same transport context. Thus the later `she_matches_certificate`
ledger obligation is derived from construction data, not supplied as an
unrelated compatibility equality.
-/
structure ConstructedQualitativeCommonContainerData
    (data : IUTStage1PreLedgerData source target index) where
  qualitativeSource : ConstructedQualitativeCertificateData data
  she_arrow_datum_eq_transport :
    data.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      qualitativeSource.sheTransportContext.sheDatum
  common_container_context_eq_transport :
    data.chartedContainer.commonContainer.context =
      qualitativeSource.sheTransportContext.baseContext.sharedContext

namespace ConstructedQualitativeCommonContainerData

variable {data : IUTStage1PreLedgerData source target index}

def ofSHEDatumAndContext
    (qualitativeSource : ConstructedQualitativeCertificateData data)
    (she_datum_eq :
      data.chartedContainer.commonContainer.hddShe.sheArrow.datum =
        qualitativeSource.sheTransportContext.sheDatum)
    (context_eq :
      data.chartedContainer.commonContainer.context =
        qualitativeSource.sheTransportContext.baseContext.sharedContext) :
    ConstructedQualitativeCommonContainerData data :=
  { qualitativeSource := qualitativeSource,
    she_arrow_datum_eq_transport := she_datum_eq,
    common_container_context_eq_transport := context_eq }

theorem certificateShe_eq_transportDatum
    (sourceData : ConstructedQualitativeCommonContainerData data) :
    data.certificate.she =
      sourceData.qualitativeSource.sheTransportContext.sheDatum := by
  simpa [
    ConstructedQualitativeCertificateData.constructedCertificate,
    QualitativeData.StructuredCertificate.ofConstructedIPLSHEAPT,
    QualitativeData.StructuredSHETransportContext.sheDatum
  ] using
    congrArg (fun certificate => certificate.she)
      sourceData.qualitativeSource.certificate_eq_constructed

theorem sheArrowDatum_eq_transportDatum
    (sourceData : ConstructedQualitativeCommonContainerData data) :
    data.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      sourceData.qualitativeSource.sheTransportContext.sheDatum := by
  exact sourceData.she_arrow_datum_eq_transport

theorem sheArrowMatchesCertificate
    (sourceData : ConstructedQualitativeCommonContainerData data) :
    data.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      data.certificate.she :=
  sourceData.sheArrowDatum_eq_transportDatum.trans
    sourceData.certificateShe_eq_transportDatum.symm

theorem commonContainerContext_eq_transportBase
    (sourceData : ConstructedQualitativeCommonContainerData data) :
    data.chartedContainer.commonContainer.context =
      sourceData.qualitativeSource.sheTransportContext.baseContext.sharedContext := by
  exact sourceData.common_container_context_eq_transport

theorem commonContainerContextMatchesCertificate
    (sourceData : ConstructedQualitativeCommonContainerData data) :
    data.chartedContainer.commonContainer.context =
      data.certificate.she.sharedContext := by
  rw [sourceData.commonContainerContext_eq_transportBase]
  rw [sourceData.certificateShe_eq_transportDatum]
  rfl

def sheArrowStructuredTransportAudit
    (sourceData : ConstructedQualitativeCommonContainerData data) :
    data.chartedContainer.commonContainer.hddShe.sheArrow.StructuredTransportAudit
      sourceData.qualitativeSource.sheTransportContext :=
  { datum_eq_context_she := sourceData.sheArrowDatum_eq_transportDatum,
    shared_context_eq_base := by
      rw [sourceData.sheArrowDatum_eq_transportDatum]
      rfl,
    forbidden_transport :=
      sourceData.qualitativeSource.sheTransportContext
        |>.domainCodomainForbiddenTransportAudit }

end ConstructedQualitativeCommonContainerData

/--
Optional source-side evidence that the pre-ledger's named hull+det bridge comes
from split hull and determinant/log-volume data.

This is the stronger audit shape needed to keep the union-of-possible-images
hull visible alongside the public endpoint.
-/
structure HullDetSourceData
    (data : IUTStage1PreLedgerData source target index) where
  structuredHullDet :
    data.output.StructuredHullDetBridgeData data.measure data.thetaSigned
  hull_det_bridge_eq :
    data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData

namespace HullDetSourceData

variable {data : IUTStage1PreLedgerData source target index}

def ofUnionSubset
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hull : Region target)
    (hsubset : Region.Subset data.output.comparisons.targetUnion hull)
    (hvolume :
      RegionMeasure.HasVolumeAtMost data.measure hull data.thetaSigned)
    (hbridge :
      data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        ((RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionSubset
            (output := data.output)
            (measure := data.measure) (bound := data.thetaSigned)
            operation hullOperation determinantOperation hull hsubset hvolume)
          |>.toHullDetHullBridgeData).toHullDetBridgeData) :
    HullDetSourceData data :=
  { structuredHullDet :=
      RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionSubset
        (output := data.output)
        (measure := data.measure) (bound := data.thetaSigned)
        operation hullOperation determinantOperation hull hsubset hvolume,
    hull_det_bridge_eq := hbridge }

def ofUnionHull
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (operator : HullOperator target)
    (hvolume :
      RegionMeasure.HasVolumeAtMost data.measure
        (operator.hull data.output.comparisons.targetUnion) data.thetaSigned)
    (hbridge :
      data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        ((RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionHull
            (output := data.output)
            (measure := data.measure) (bound := data.thetaSigned)
            operation hullOperation determinantOperation operator hvolume)
          |>.toHullDetHullBridgeData).toHullDetBridgeData) :
    HullDetSourceData data :=
  { structuredHullDet :=
      RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionHull
        (output := data.output)
        (measure := data.measure) (bound := data.thetaSigned)
        operation hullOperation determinantOperation operator hvolume,
    hull_det_bridge_eq := hbridge }

def stepAudit (sourceData : HullDetSourceData data) :
    sourceData.structuredHullDet.StepAudit data.certificate :=
  sourceData.structuredHullDet.stepAudit data.certificate

theorem targetUnion_subset_hull
    (sourceData : HullDetSourceData data) :
    Region.Subset data.output.comparisons.targetUnion
      (sourceData.structuredHullDet.applyHull data.certificate).hull :=
  sourceData.stepAudit.targetUnion_subset_hull

theorem determinantVolumeBound
    (sourceData : HullDetSourceData data) :
    RegionMeasure.HasVolumeAtMost data.measure
      (sourceData.structuredHullDet.applyHull data.certificate).hull
      data.thetaSigned :=
  sourceData.stepAudit.determinantVolumeBound

theorem hullDetBridge_eq
    (sourceData : HullDetSourceData data) :
    data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
      sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData :=
  sourceData.hull_det_bridge_eq

theorem choiceTargetVolume_le_thetaSigned
    (sourceData : HullDetSourceData data) (choice : index) :
    RegionMeasure.targetVolume data.measure (data.output.comparison choice) <=
      data.thetaSigned :=
  sourceData.stepAudit.choiceTargetVolume_le choice

theorem allTargetsAtMost
    (sourceData : HullDetSourceData data) :
    RegionComparisonFamily.AllTargetsAtMost data.measure data.output.comparisons
      data.thetaSigned :=
  sourceData.stepAudit.allTargetsAtMost

theorem ofUnionSubset_endpoint
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (hull : Region target)
    (hsubset : Region.Subset data.output.comparisons.targetUnion hull)
    (hvolume :
      RegionMeasure.HasVolumeAtMost data.measure hull data.thetaSigned)
    (hbridge :
      data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        ((RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionSubset
            (output := data.output)
            (measure := data.measure) (bound := data.thetaSigned)
            operation hullOperation determinantOperation hull hsubset hvolume)
          |>.toHullDetHullBridgeData).toHullDetBridgeData) :
    let sourceData :=
      ofUnionSubset (data := data)
        operation hullOperation determinantOperation hull hsubset hvolume hbridge;
    Region.Subset data.output.comparisons.targetUnion
        (sourceData.structuredHullDet.applyHull data.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost data.measure
        (sourceData.structuredHullDet.applyHull data.certificate).hull
        data.thetaSigned ∧
      RegionComparisonFamily.AllTargetsAtMost data.measure data.output.comparisons
        data.thetaSigned ∧
      data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData :=
  by
    intro sourceData
    exact
      ⟨sourceData.targetUnion_subset_hull,
        sourceData.determinantVolumeBound,
        sourceData.allTargetsAtMost,
        sourceData.hullDetBridge_eq⟩

theorem ofUnionHull_endpoint
    (operation : RealLineCopy.AlgorithmicOutput.HullDetOperationId)
    (hullOperation : RealLineCopy.AlgorithmicOutput.HullOperationId)
    (determinantOperation :
      RealLineCopy.AlgorithmicOutput.DeterminantLogVolumeOperationId)
    (operator : HullOperator target)
    (hvolume :
      RegionMeasure.HasVolumeAtMost data.measure
        (operator.hull data.output.comparisons.targetUnion) data.thetaSigned)
    (hbridge :
      data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        ((RealLineCopy.AlgorithmicOutput.StructuredHullDetBridgeData.ofUnionHull
            (output := data.output)
            (measure := data.measure) (bound := data.thetaSigned)
            operation hullOperation determinantOperation operator hvolume)
          |>.toHullDetHullBridgeData).toHullDetBridgeData) :
    let sourceData :=
      ofUnionHull (data := data)
        operation hullOperation determinantOperation operator hvolume hbridge;
    (sourceData.structuredHullDet.applyHull data.certificate).hull =
        operator.hull data.output.comparisons.targetUnion ∧
      Region.Subset data.output.comparisons.targetUnion
        (sourceData.structuredHullDet.applyHull data.certificate).hull ∧
      RegionMeasure.HasVolumeAtMost data.measure
        (sourceData.structuredHullDet.applyHull data.certificate).hull
        data.thetaSigned ∧
      RegionComparisonFamily.AllTargetsAtMost data.measure data.output.comparisons
        data.thetaSigned ∧
      data.chartedContainer.commonContainer.hddShe.hdd.hullDetBridge =
        sourceData.structuredHullDet.toHullDetHullBridgeData.toHullDetBridgeData :=
  by
    intro sourceData
    exact
      ⟨rfl,
        sourceData.targetUnion_subset_hull,
        sourceData.determinantVolumeBound,
        sourceData.allTargetsAtMost,
        sourceData.hullDetBridge_eq⟩

end HullDetSourceData

/--
Remaining obligations required to promote pre-ledger data to a full source
ledger.

The opaque `certified` field is intentionally separate from the structured
certificate: a structured family-level certificate is not automatically evidence
for the opaque propositions stored by `AlgorithmicOutput`.
-/
structure LedgerPromotionObligations
    (data : IUTStage1PreLedgerData source target index) : Prop where
  certified : data.output.Certified
  she_matches_certificate :
    data.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      data.certificate.she
  q_positive : 0 < -data.qSigned
  normalization_proof : data.normalization

/--
Promotion obligations whose SHE/certificate alignment is derived from the
constructed qualitative common-container source.

This is the constructor-backed promotion path for the 3.11-to-3.12 ledger:
certification, q-positivity, and normalization remain explicit lower-level
obligations, while the previous standalone `she_matches_certificate` equality
is obtained from the constructed IPL/SHE/APT certificate and common container.
-/
structure ConstructedLedgerPromotionObligations
    (data : IUTStage1PreLedgerData source target index) where
  certified : data.output.Certified
  constructedCommonContainer :
    ConstructedQualitativeCommonContainerData data
  q_positive : 0 < -data.qSigned
  normalization_proof : data.normalization

namespace ConstructedLedgerPromotionObligations

variable {data : IUTStage1PreLedgerData source target index}

theorem sheMatchesCertificate
    (obligations : ConstructedLedgerPromotionObligations data) :
    data.chartedContainer.commonContainer.hddShe.sheArrow.datum =
      data.certificate.she :=
  obligations.constructedCommonContainer.sheArrowMatchesCertificate

theorem commonContainerContextMatchesCertificate
    (obligations : ConstructedLedgerPromotionObligations data) :
    data.chartedContainer.commonContainer.context =
      data.certificate.she.sharedContext :=
  obligations.constructedCommonContainer.commonContainerContextMatchesCertificate

def toLedgerPromotionObligations
    (obligations : ConstructedLedgerPromotionObligations data) :
    LedgerPromotionObligations data :=
  { certified := obligations.certified,
    she_matches_certificate := obligations.sheMatchesCertificate,
    q_positive := obligations.q_positive,
    normalization_proof := obligations.normalization_proof }

theorem toLedgerPromotionObligations_she_matches_certificate
    (obligations : ConstructedLedgerPromotionObligations data) :
    obligations.toLedgerPromotionObligations.she_matches_certificate =
      obligations.sheMatchesCertificate :=
  rfl

def toSourceObligationLedger
    (obligations : ConstructedLedgerPromotionObligations data) :
    SourceObligationLedger
      data.output data.measure data.thetaSigned data.qSigned data.normalization :=
  { certified := obligations.certified,
    certificate := data.certificate,
    chartedContainer := data.chartedContainer,
    she_matches_certificate := obligations.sheMatchesCertificate,
    qValue := data.qValue,
    thetaBound := data.thetaBound,
    theta_commonBound := data.chartedContainer.apply data.certificate,
    theta_commonBound_eq_charted := rfl,
    chosenOutput := data.chosenOutput,
    targetVolume := data.targetVolume,
    membership := data.membership,
    q_positive := obligations.q_positive,
    normalization_proof := obligations.normalization_proof }

theorem toSourceObligationLedger_sheMatchesCertificate
    (obligations : ConstructedLedgerPromotionObligations data) :
    obligations.toSourceObligationLedger.sheMatchesCertificate =
      obligations.sheMatchesCertificate :=
  rfl

def toSourceObligationProvider
    (obligations : ConstructedLedgerPromotionObligations data) :
    IUTSourceObligationProvider
      data.output data.measure data.thetaSigned data.qSigned data.normalization :=
  { ledger := obligations.toSourceObligationLedger }

theorem toSourceObligationProvider_publicAudit
    (obligations : ConstructedLedgerPromotionObligations data) :
    data.qSigned <= data.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta data.thetaSigned)
        (signedPilotLogVolume PilotSide.q data.qSigned) ∧
      corollary312_from_stage1_comparison
          obligations.toSourceObligationProvider.ledger.stage1Comparison =
        corollary312_of_signed_le
          obligations.toSourceObligationProvider.ledger.qSigned_le_thetaSigned :=
  obligations.toSourceObligationProvider.ledger.publicAudit

end ConstructedLedgerPromotionObligations

def toSourceObligationLedger
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    SourceObligationLedger
      data.output data.measure data.thetaSigned data.qSigned data.normalization :=
  { certified := obligations.certified,
    certificate := data.certificate,
    chartedContainer := data.chartedContainer,
    she_matches_certificate := obligations.she_matches_certificate,
    qValue := data.qValue,
    thetaBound := data.thetaBound,
    theta_commonBound := data.chartedContainer.apply data.certificate,
    theta_commonBound_eq_charted := rfl,
    chosenOutput := data.chosenOutput,
    targetVolume := data.targetVolume,
    membership := data.membership,
    q_positive := obligations.q_positive,
    normalization_proof := obligations.normalization_proof }

def toSourceObligationProvider
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    IUTSourceObligationProvider
      data.output data.measure data.thetaSigned data.qSigned data.normalization :=
  { ledger := data.toSourceObligationLedger obligations }

def promotedLedger
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    SourceObligationLedger
      data.output data.measure data.thetaSigned data.qSigned data.normalization :=
  data.toSourceObligationLedger obligations

def promotedProvider
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    IUTSourceObligationProvider
      data.output data.measure data.thetaSigned data.qSigned data.normalization :=
  data.toSourceObligationProvider obligations

theorem promotedProvider_ledger
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    (data.promotedProvider obligations).ledger =
      data.promotedLedger obligations :=
  rfl

theorem toSourceObligationLedger_audit
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    SourceObligationLedger.Audit
      (data.toSourceObligationLedger obligations) :=
  (data.toSourceObligationLedger obligations).audit

theorem toSourceObligationProvider_publicAudit
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    data.qSigned <= data.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta data.thetaSigned)
        (signedPilotLogVolume PilotSide.q data.qSigned) ∧
      (corollary312_from_stage1_comparison
          (data.toSourceObligationProvider obligations).stage1Comparison =
        corollary312_of_signed_le
          (data.toSourceObligationProvider obligations).ledger.qSigned_le_thetaSigned) :=
  (data.toSourceObligationProvider obligations).publicAudit

theorem publicAudit
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    data.qSigned <= data.thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta data.thetaSigned)
        (signedPilotLogVolume PilotSide.q data.qSigned) ∧
      (corollary312_from_stage1_comparison
          (data.toSourceObligationProvider obligations).stage1Comparison =
        corollary312_of_signed_le
          (data.toSourceObligationProvider obligations).ledger.qSigned_le_thetaSigned) :=
  data.toSourceObligationProvider_publicAudit obligations

theorem publicAudit_qSigned_le_thetaSigned
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    data.qSigned <= data.thetaSigned :=
  (data.publicAudit obligations).1

theorem publicAudit_corollary312
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta data.thetaSigned)
      (signedPilotLogVolume PilotSide.q data.qSigned) :=
  (data.publicAudit obligations).2.1

theorem publicAudit_stage1Comparison_recovers_qSigned_le_thetaSigned
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    corollary312_from_stage1_comparison
        (data.toSourceObligationProvider obligations).stage1Comparison =
      corollary312_of_signed_le
        (data.toSourceObligationProvider obligations).ledger.qSigned_le_thetaSigned :=
  (data.publicAudit obligations).2.2

theorem stage1Comparison_recovers_corollary312
    (data : IUTStage1PreLedgerData source target index)
    (obligations : LedgerPromotionObligations data) :
    corollary312_from_stage1_comparison
        (data.toSourceObligationProvider obligations).stage1Comparison =
      (data.toSourceObligationProvider obligations).ledger.corollary312 :=
  (data.toSourceObligationProvider obligations).stage1Comparison_recovers_corollary312

end IUTStage1PreLedgerData

end Stage1
end Iut
