/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1FrobenioidShift

/-!
Endpoint-audit refinements for the Stage 1 source-facing route.

This module isolates the nested LogVolumeChartAudit refinements around the
place-audited multiradial theta-hull endpoint.  The public source package route
continues in IUTStage1Source.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

namespace IUTStage1SourcePackage

variable {source target : Copy} {index : Type u}

namespace PlaceAuditedMultiradialThetaHullEndpoint

variable {coric : Type u} {kind : IUTStage1PlaceKind}
variable
  {package :
    IUTStage1SourcePackage source target
      (IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)}
variable {obligations : IUTStage1SourceHullDetObligations package}

namespace LogVolumeChartAudit

variable {endpoint : package.PlaceAuditedMultiradialThetaHullEndpoint obligations}

namespace FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    cuspClassLocalObject_eq_packetLocalObject := by
      intro audited label
      exact
        (part.localObjectTransport audited).cuspClass_transports_to_packet'
          label,
    zeroLocalObject_eq_packetLocalObject := by
      intro audited
      exact (part.localObjectTransport audited).zero_transports_to_packet' }

def toHodgeDescentInsulatedCuspZeroBridgeAudit
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaHodgeDescentInsulatedCuspZeroBridgeAudit l :=
  let transport := part.toHodgeDescentPacketTransportAudit
  transport.toHodgeDescentInsulatedCuspZeroBridgeAudit

theorem localObjectTransport_checkpoint_eq_fourthTriangle
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.bundle.hodgeTheaterDescentBridgeData.zeroColumnCheckpoint =
      fourthTriangleHDDSHECheckpoint :=
  (part.localObjectTransport audited).checkpoint_eq_fourthTriangle

def localObjectSquareWeightBoundary
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1LocalObjectHodgeDescentSquareWeightBoundary
      l part.bundle.hodgeTheaterDescentBridgeData
      (part.insulated_route.zeroLocalObject audited)
      (part.insulated_route.cuspClassLocalObject audited)
      audited.choice.local_tensor_state.packetState.localObject :=
  { localObjectTransport := part.localObjectTransport audited }

theorem localObjectSquareWeightBoundary_coordinateEquiv_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1SquareWeightTransportMissingDatum.coordinateEquiv ∈
      (part.localObjectSquareWeightBoundary audited).missingSquareWeightData :=
  (part.localObjectSquareWeightBoundary audited).coordinateEquiv_missing

theorem localObjectSquareWeightBoundary_squareWeightPreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1SquareWeightTransportMissingDatum.squareWeightPreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingSquareWeightData :=
  (part.localObjectSquareWeightBoundary audited).squareWeightPreservation_missing

theorem localObjectSquareWeightBoundary_fullLabelPreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1SquareWeightTransportMissingDatum.fullLabelLogVolumePreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingSquareWeightData :=
  (part.localObjectSquareWeightBoundary audited).fullLabelLogVolumePreservation_missing

theorem localObjectSquareWeightBoundary_coordinateSquarePreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1FactoredSquareFullLabelMissingDatum.coordinateSquarePreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingFactoredSquareFullLabelData :=
  (part.localObjectSquareWeightBoundary audited).coordinateSquarePreservation_missing

theorem localObjectSquareWeightBoundary_fullLabelMapPreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelMapPreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingFactoredSquareFullLabelData :=
  (part.localObjectSquareWeightBoundary audited).fullLabelMapPreservation_missing

theorem localObjectSquareWeightBoundary_fullLabelValuePreservation_missing
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    IUTStage1FactoredSquareFullLabelMissingDatum.fullLabelValuePreservation ∈
      (part.localObjectSquareWeightBoundary audited).missingFactoredSquareFullLabelData :=
  (part.localObjectSquareWeightBoundary audited).fullLabelValuePreservation_missing

theorem zeroLocalObject_eq_packetLocalObject
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.insulated_route.zeroLocalObject audited =
      audited.choice.local_tensor_state.packetState.localObject :=
  (part.localObjectTransport audited).zero_transports_to_packet'

theorem cuspClassLocalObject_eq_packetLocalObject
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.cuspClassLocalObject audited label =
      audited.choice.local_tensor_state.packetState.localObject :=
  (part.localObjectTransport audited).cuspClass_transports_to_packet' label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectTransport audited).zero_eq_cuspClass label

theorem bridgeSource_eq_hodgeTheaterDescentPacketTransport
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l) :
    let transport := part.toHodgeDescentPacketTransportAudit
    transport.toHodgeDescentInsulatedCuspZeroBridgeAudit.classified_bridge.bridge_source =
      IUTStage1ZModPacketLocalObjectBridgeSource.hodgeTheaterDescentPacketTransport :=
  let transport := part.toHodgeDescentPacketTransportAudit
  transport.bridgeSource_eq_hodgeTheaterDescentPacketTransport

theorem comparisonSource_eq_hodgeTheaterDescent
    (part :
      audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l) :
    let transport := part.toHodgeDescentPacketTransportAudit
    let hodgeBridge := transport.toHodgeDescentInsulatedCuspZeroBridgeAudit
    hodgeBridge.toSourcedInsulatedCuspZeroPacketBridgeAudit.comparison_source =
      IUTStage1InsulatedCuspZeroBridgeSource.hodgeTheaterDescentIndeterminacy :=
  let transport := part.toHodgeDescentPacketTransportAudit
  transport.comparisonSource_eq_hodgeTheaterDescent

end FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toStructuredHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    localObjectTransport := fun audited =>
      (part.localObjectOperation audited).toLocalObjectTransportData }

def toHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaHodgeDescentPacketTransportAudit l :=
  let structured := part.toStructuredHodgeDescentPacketTransportAudit
  structured.toHodgeDescentPacketTransportAudit

theorem zeroOperation_descent_eq_hodgeData
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    (part.localObjectOperation audited).zeroOperation.descent =
      part.bundle.hodgeTheaterDescentBridgeData.descent :=
  (part.localObjectOperation audited).zeroOperation_descent_eq_hodgeData

theorem cuspClassOperation_descent_eq_hodgeData
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    ((part.localObjectOperation audited).cuspClassOperation label).descent =
      part.bundle.hodgeTheaterDescentBridgeData.descent :=
  (part.localObjectOperation audited).cuspClassOperation_descent_eq_hodgeData
    label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectOperation audited).zero_eq_cuspClass label

theorem bridgeSource_eq_hodgeTheaterDescentPacketTransport
    (part :
      audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l) :
    let structured := part.toStructuredHodgeDescentPacketTransportAudit
    let transport := structured.toHodgeDescentPacketTransportAudit
    transport.toHodgeDescentInsulatedCuspZeroBridgeAudit.classified_bridge.bridge_source =
      IUTStage1ZModPacketLocalObjectBridgeSource.hodgeTheaterDescentPacketTransport :=
  let structured := part.toStructuredHodgeDescentPacketTransportAudit
  structured.bridgeSource_eq_hodgeTheaterDescentPacketTransport

end FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toOperatedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    localObjectOperation := fun audited =>
      (part.localObjectOperation audited).toCuspZeroLocalObjectOperationData }

def toStructuredHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaStructuredHodgeDescentPacketTransportAudit l :=
  let operated := part.toOperatedHodgeDescentPacketTransportAudit
  operated.toStructuredHodgeDescentPacketTransportAudit

theorem zeroSourceRole_eq
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    (part.localObjectOperation audited).zeroOperation.sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.zeroColumnSHEInput :=
  (part.localObjectOperation audited).zeroSourceRole_eq

theorem cuspClassSourceRole_eq
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    ((part.localObjectOperation audited).cuspClassOperation label).sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.cuspClassHodgeArakelovEvaluation :=
  (part.localObjectOperation audited).cuspClassSourceRole_eq label

theorem zeroTargetRole_eq_packet
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    (part.localObjectOperation audited).zeroOperation.targetRole =
      IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget :=
  (part.localObjectOperation audited).zeroTargetRole_eq_packet

theorem cuspClassTargetRole_eq_packet
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    ((part.localObjectOperation audited).cuspClassOperation label).targetRole =
      IUTStage1HodgeDescentLocalObjectRole.packetDescentTarget :=
  (part.localObjectOperation audited).cuspClassTargetRole_eq_packet label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectOperation audited).zero_eq_cuspClass label

end FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toRoleMarkedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    localObjectOperation := fun audited =>
      (part.localObjectOperation audited).toRoleMarkedCuspZeroLocalObjectOperationData }

def toOperatedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaOperatedHodgeDescentPacketTransportAudit l :=
  let roleMarked := part.toRoleMarkedHodgeDescentPacketTransportAudit
  roleMarked.toOperatedHodgeDescentPacketTransportAudit

theorem zeroSource_checkpoint_eq_fourthTriangle
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.bundle.hodgeTheaterDescentBridgeData.zeroColumnCheckpoint =
      fourthTriangleHDDSHECheckpoint :=
  (part.localObjectOperation audited).zeroSource_checkpoint_eq_fourthTriangle

theorem cuspClassSource_checkpoint_eq_fourthTriangle
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.bundle.hodgeTheaterDescentBridgeData.zeroColumnCheckpoint =
      fourthTriangleHDDSHECheckpoint :=
  (part.localObjectOperation audited).cuspClassSource_checkpoint_eq_fourthTriangle
    label

theorem packetTarget_descent_eq_hodgeData
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    (part.localObjectOperation audited).packetTarget.descent =
      part.bundle.hodgeTheaterDescentBridgeData.descent :=
  (part.localObjectOperation audited).packetTarget_descent_eq_hodgeData

theorem zeroSourceRole_eq
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    ((part.toRoleMarkedHodgeDescentPacketTransportAudit).localObjectOperation
        audited).zeroOperation.sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.zeroColumnSHEInput :=
  let roleMarked := part.toRoleMarkedHodgeDescentPacketTransportAudit
  roleMarked.zeroSourceRole_eq audited

theorem cuspClassSourceRole_eq
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    let roleMarked := part.toRoleMarkedHodgeDescentPacketTransportAudit
    ((roleMarked.localObjectOperation audited).cuspClassOperation label).sourceRole =
      IUTStage1HodgeDescentLocalObjectRole.cuspClassHodgeArakelovEvaluation :=
  let roleMarked := part.toRoleMarkedHodgeDescentPacketTransportAudit
  roleMarked.cuspClassSourceRole_eq audited label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectOperation audited).zero_eq_cuspClass label

end FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toSourceMarkedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaSourceMarkedHodgeDescentPacketTransportAudit l :=
  { bundle := part.bundle,
    insulated_route := part.insulated_route,
    packetLocalObjectEstimate := part.packetLocalObjectEstimate,
    packetLocalObjectEstimate_eq_packetLocalObject :=
      part.packetLocalObjectEstimate_eq_packetLocalObject,
    localObjectOperation := fun audited =>
      let operation := part.localObjectOperation audited
      operation.toSourceMarkedCuspZeroLocalObjectOperationData }

def toRoleMarkedHodgeDescentPacketTransportAudit
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l) :
    audit.FLZModCuspLabelThetaRoleMarkedHodgeDescentPacketTransportAudit l :=
  let sourceMarked := part.toSourceMarkedHodgeDescentPacketTransportAudit
  sourceMarked.toRoleMarkedHodgeDescentPacketTransportAudit

theorem cuspClassLabel_eq_zmodCoordinate
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    label =
      zmodSignLabelFromCoordinate l
        ((part.localObjectOperation audited).cuspClassSource label).coordinate
        ((part.localObjectOperation audited).cuspClassSource label).coordinate_ne_zero :=
  (part.localObjectOperation audited).cuspClassLabel_eq_zmodCoordinate label

theorem cuspClassLabel_eq_negCoordinate
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    label =
      zmodSignLabelFromCoordinate l
        (-((part.localObjectOperation audited).cuspClassSource label).coordinate)
        (zmod_neg_ne_zero_of_ne_zero l
          ((part.localObjectOperation audited).cuspClassSource label).coordinate_ne_zero) :=
  (part.localObjectOperation audited).cuspClassLabel_eq_negCoordinate label

theorem cuspClassLabel_eq_canonical_of_coordinate_eq_one
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient)
    (hcoord :
      ((part.localObjectOperation audited).cuspClassSource label).coordinate =
        (1 : ZMod l.value)) :
    label = zmodCanonicalSignLabelQuotient l :=
  (part.localObjectOperation audited).cuspClassLabel_eq_canonical_of_coordinate_eq_one
    label hcoord

def fullLabelLocalObject
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : IUTStage1ZModCuspFullLabel l) :
    IUTStage1FiniteLocalLogVolumeObject kind :=
  (part.localObjectOperation audited).fullLabelLocalObject label

theorem fullLabelLocalObject_zero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.fullLabelLocalObject audited IUTStage1ZModCuspFullLabel.zero =
      part.insulated_route.zeroLocalObject audited :=
  rfl

theorem fullLabelLocalObject_nonzero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.fullLabelLocalObject audited
        (IUTStage1ZModCuspFullLabel.nonzero label) =
      part.insulated_route.cuspClassLocalObject audited label :=
  rfl

theorem fullLabelLocalObject_transports_to_packet
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : IUTStage1ZModCuspFullLabel l) :
    part.fullLabelLocalObject audited label =
      audited.choice.local_tensor_state.packetState.localObject :=
  (part.localObjectOperation audited).fullLabelLocalObject_transports_to_packet label

theorem fullLabelLocalObject_fromCoordinate_zero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.fullLabelLocalObject audited
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (0 : ZMod l.value)) =
      part.insulated_route.zeroLocalObject audited := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
  rfl

theorem fullLabelLocalObject_fromCoordinate_nonzero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (j : ZMod l.value) (hj : j ≠ 0) :
    part.fullLabelLocalObject audited
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      part.insulated_route.cuspClassLocalObject audited
        (zmodSignLabelFromCoordinate l j hj) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj]
  rfl

theorem cuspClassCoordinate_ne_zero
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    ((part.localObjectOperation audited).cuspClassSource label).coordinate ≠ 0 :=
  (part.localObjectOperation audited).cuspClassCoordinate_ne_zero label

theorem zeroLocalObject_eq_cuspClassLocalObject
    (part :
      audit.FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    part.insulated_route.zeroLocalObject audited =
      part.insulated_route.cuspClassLocalObject audited label :=
  (part.localObjectOperation audited).zero_eq_cuspClass label

end FLZModCuspLabelThetaZModSourceMarkedHodgeDescentPacketTransportAudit

namespace FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toZModPacketNormalizedRouteAudit
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    audit.FLZModCuspLabelThetaZModPacketNormalizedRouteAudit l :=
  part.toDirectPacketNormalizedLocalObjectRouteAudit.toZModPacketNormalizedRouteAudit

def toConstantZModPacketNormalizedRouteAudit
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    audit.FLZModCuspLabelThetaConstantZModPacketNormalizedRouteAudit l :=
  part.toZModPacketNormalizedRouteAudit.toConstantZModPacketNormalizedRouteAudit

theorem thetaSourceAverage_eq_packetNormalized
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    part.theta_source.thetaSourceAverage audited =
      audited.choice.local_tensor_state.packetState.capsuleFamily.normalizedLogVolume :=
  let constantRoute := part.toConstantZModPacketNormalizedRouteAudit
  constantRoute.thetaSourceAverage_eq_packetNormalized audited

theorem targetSigned_le_thetaSourceAverage
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.theta_source.thetaSourceAverage audited :=
  let constantRoute := part.toConstantZModPacketNormalizedRouteAudit
  constantRoute.targetSigned_le_thetaSourceAverage audited

def toInsulatedCuspZeroPacketBridgeAudit
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    audit.FLZModCuspLabelThetaInsulatedCuspZeroPacketBridgeAudit l :=
  { insulated_route :=
      { theta_source := part.theta_source,
        ind12_equality_part := part.ind12_equality_part,
        ind3_upper_part := part.ind3_upper_part,
        theta_images_eq_endpoint := part.theta_images_eq_endpoint,
        cuspClassLocalObject := by
          intro audited _label
          exact audited.choice.local_tensor_state.packetState.localObject,
        cuspClassLogVolume_eq_localObjectFinite :=
          part.cuspClassLogVolume_eq_localObjectFinite,
        zeroLocalObject := by
          intro audited
          exact audited.choice.local_tensor_state.packetState.localObject,
        zeroLogVolume_eq_localObjectFinite :=
          part.zeroLogVolume_eq_localObjectFinite },
    packetLocalObjectEstimate := by
      intro audited
      exact
        (part.directNormalization audited).toLocalObjectContainerEstimateOfCapsuleEstimates
          (part.targetCapsuleEstimates audited),
    packetLocalObjectEstimate_eq_packetLocalObject := by
      intro _audited
      rfl,
    cuspClassLocalObject_eq_packetLocalObject := by
      intro _audited _label
      rfl,
    zeroLocalObject_eq_packetLocalObject := by
      intro _audited
      rfl }

open FLZModCuspLabelThetaClassifiedInsulatedCuspZeroPacketBridgeAudit in
def toClassifiedInsulatedCuspZeroPacketBridgeAudit
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    audit.FLZModCuspLabelThetaClassifiedInsulatedCuspZeroPacketBridgeAudit l :=
  ofDirectLocalLabelObjectConstruction
    part.toInsulatedCuspZeroPacketBridgeAudit

theorem insulatedPacketBridgeSource_eq_direct
    (part :
      audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l) :
    part.toClassifiedInsulatedCuspZeroPacketBridgeAudit.bridge_source =
      IUTStage1ZModPacketLocalObjectBridgeSource.directLocalLabelObjectConstruction :=
  rfl

end FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit

namespace FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toDirectIdentifiedLocalPacketRouteAudit
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaDirectIdentifiedLocalPacketRouteAudit l :=
  { theta_source := part.direct_packet.theta_source,
    ind12_equality_part := part.direct_packet.ind12_equality_part,
    ind3_upper_part := part.direct_packet.ind3_upper_part,
    theta_images_eq_endpoint := part.direct_packet.theta_images_eq_endpoint,
    targetCapsuleEstimates := part.targetCapsuleEstimates,
    directNormalization := part.direct_packet.zeroDirectNormalization,
    cuspClassLogVolume_eq_localObjectFinite := by
      intro audited label
      let estimate := part.direct_packet.cuspClassObjectEstimate audited label
      calc
        (part.direct_packet.theta_source.compatible_average.cuspLogVolume
          audited).cuspClassLogVolume label =
            estimate.localObject.finiteLogVolume :=
          estimate.localLogVolume_eq_object
        _ =
            audited.choice.local_tensor_state.packetState.localObject.finiteLogVolume := by
          rw [part.direct_packet.cuspClassObject_eq_packetLocalObject audited label],
    zeroLogVolume_eq_localObjectFinite := by
      intro audited
      let estimate := part.direct_packet.zeroObjectEstimate audited
      calc
        (part.direct_packet.theta_source.compatible_average.cuspLogVolume
          audited).zeroLogVolume =
            estimate.localObject.finiteLogVolume :=
          estimate.localLogVolume_eq_object
        _ =
            audited.choice.local_tensor_state.packetState.localObject.finiteLogVolume := by
          rw [part.direct_packet.zeroObject_eq_packetLocalObject audited] }

def toDirectCapsuleCuspClassAudit
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaDirectCapsuleCuspClassAudit l :=
  { packet_normalized :=
      part.direct_packet.toClassifiedPacketNormalizedAudit.packet_normalized,
    targetCapsuleEstimates := part.targetCapsuleEstimates }

def toFullClassifiedRouteSummary
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaFullClassifiedRouteSummary l :=
  let packetSummary := part.direct_packet.toClassifiedPacketNormalizedAudit
  let direct := part.toDirectCapsuleCuspClassAudit
  FLZModCuspLabelThetaFullClassifiedRouteSummary.ofDirectCapsule
    packetSummary direct rfl

theorem packetIdentificationSource_eq_direct
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    part.toFullClassifiedRouteSummary.packetIdentificationSource =
      IUTStage1PacketNormalizedIdentificationSource.directPacketNormalization :=
  rfl

theorem cuspBoundSource_eq_directCapsule
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l) :
    part.toFullClassifiedRouteSummary.cuspBoundSource =
      IUTStage1CuspClassBoundSource.directCapsuleEstimates :=
  rfl

theorem targetSigned_le_thetaSourceAverage
    (part :
      audit.FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.direct_packet.theta_source.thetaSourceAverage audited :=
  let identifiedRoute := part.toDirectIdentifiedLocalPacketRouteAudit
  identifiedRoute.targetSigned_le_thetaSourceAverage audited

end FLZModCuspLabelThetaDirectLocalPacketDirectCapsuleRouteAudit

namespace FLZModCuspLabelThetaPacketLocalObjectContainerAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

theorem targetSigned_le_thetaSourceAverage_of_directPacket
    (part : audit.FLZModCuspLabelThetaPacketLocalObjectContainerAudit l)
    (directNormalization :
      ∀ audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind,
        IUTStage1DirectPacketNormalizationData
          audited.choice.local_tensor_state.packetState)
    (targetCapsuleEstimates :
      ∀ audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind,
        IUTStage1TypedCapsuleFamilyContainerEstimate
          package.preLedger.targetVolume.targetSigned
          audited.choice.local_tensor_state.packetState.capsuleFamily)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.theta_source.thetaSourceAverage audited := by
  let directRoute :=
    part.toDirectLocalPacketDirectCapsuleRouteAudit
      directNormalization targetCapsuleEstimates
  exact directRoute.targetSigned_le_thetaSourceAverage audited

end FLZModCuspLabelThetaPacketLocalObjectContainerAudit

namespace FLZModCuspLabelThetaClassifiedPacketLocalObjectContainerAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

theorem targetSigned_le_thetaSourceAverage_of_directPacket
    (part : audit.FLZModCuspLabelThetaClassifiedPacketLocalObjectContainerAudit l)
    (directNormalization :
      ∀ audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind,
        IUTStage1DirectPacketNormalizationData
          audited.choice.local_tensor_state.packetState)
    (targetCapsuleEstimates :
      ∀ audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind,
        IUTStage1TypedCapsuleFamilyContainerEstimate
          package.preLedger.targetVolume.targetSigned
          audited.choice.local_tensor_state.packetState.capsuleFamily)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.packet_local_object.theta_source.thetaSourceAverage audited :=
  part.packet_local_object.targetSigned_le_thetaSourceAverage_of_directPacket
    directNormalization targetCapsuleEstimates audited

end FLZModCuspLabelThetaClassifiedPacketLocalObjectContainerAudit

namespace FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def toInd2TransportedCuspClassAudit
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaInd2TransportedCuspClassAudit l :=
  { packet_normalized :=
      part.ind2_packet.toClassifiedPacketNormalizedAudit.packet_normalized,
    sourceAudited := part.ind2_packet.sourceAudited,
    ind2_step := part.ind2_packet.ind2_step,
    sourceCapsuleEstimates := part.sourceCapsuleEstimates }

def toFullClassifiedRouteSummary
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l) :
    audit.FLZModCuspLabelThetaFullClassifiedRouteSummary l :=
  let packetSummary := part.ind2_packet.toClassifiedPacketNormalizedAudit
  let transported := part.toInd2TransportedCuspClassAudit
  FLZModCuspLabelThetaFullClassifiedRouteSummary.ofInd2Transport
    packetSummary transported rfl

theorem packetIdentificationSource_eq_ind2Transported
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l) :
    part.toFullClassifiedRouteSummary.packetIdentificationSource =
      IUTStage1PacketNormalizedIdentificationSource.ind2TransportedPacketNormalization :=
  rfl

theorem cuspBoundSource_eq_ind2Transported
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l) :
    part.toFullClassifiedRouteSummary.cuspBoundSource =
      IUTStage1CuspClassBoundSource.ind2TransportedCapsuleEstimates :=
  rfl

theorem targetSigned_le_thetaSourceAverage
    (part :
      audit.FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.ind2_packet.theta_source.thetaSourceAverage audited :=
  let transported := part.toInd2TransportedCuspClassAudit
  transported.targetSigned_le_thetaAverage audited

end FLZModCuspLabelThetaInd2LocalPacketTransportedCapsuleRouteAudit

namespace FLZModCuspLabelThetaContainerBoundAudit

variable {audit : endpoint.LogVolumeChartAudit}
variable {l : PrimeGeFive}

def comparisonLevel
    (_part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.hullLogVolume

theorem comparisonLevel_eq_hullLogVolume
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    part.comparisonLevel =
      IUTStage1SquareComparisonLevel.hullLogVolume :=
  rfl

theorem comparisonLevel_ne_pointwiseRepresentative
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    part.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.pointwiseRepresentative :=
  IUTStage1SquareComparisonLevel.hull_ne_pointwise

theorem comparisonLevel_ne_aggregateRepresentative
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    part.comparisonLevel ≠
      IUTStage1SquareComparisonLevel.aggregateRepresentative :=
  IUTStage1SquareComparisonLevel.hull_ne_aggregate

theorem comparisonLevel_ne_structuredSHEFactored
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    {bundle : IUTStage1Theorem311StructuredInputsWithSHE package}
    (obligations :
      IUTStage1StructuredSHEFactoredSquareFullLabelObligations
        package bundle l) :
    part.comparisonLevel ≠ obligations.comparisonLevel := by
  rw [part.comparisonLevel_eq_hullLogVolume,
    obligations.comparisonLevel_eq_pointwiseRepresentative]
  exact IUTStage1SquareComparisonLevel.hull_ne_pointwise

theorem comparisonLevel_ne_squareWeightedAverage
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (averagePart : audit.FLZModCuspLabelCompatibleAveragedInd12Audit l) :
    part.comparisonLevel ≠
      averagePart.squareWeightedAverageComparisonLevel := by
  rw [part.comparisonLevel_eq_hullLogVolume,
    averagePart.squareWeightedAverageComparisonLevel_eq_aggregate]
  exact IUTStage1SquareComparisonLevel.hull_ne_aggregate

theorem boundSource_not_ind3Only
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    part.bound_source ≠ IUTStage1TargetAverageBoundSource.ind3UpperSemiOnly :=
  part.bound_source_not_ind3_only

theorem targetSigned_le_thetaAverage'
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <=
      part.theta_source.thetaSourceAverage audited :=
  part.targetSigned_le_thetaAverage audited

theorem ind3TargetSigned_le_thetaSigned
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    package.preLedger.targetVolume.targetSigned <=
      package.preLedger.thetaSigned :=
  part.ind3_upper_part.targetSigned_le_thetaSigned

def toTargetAverageReductionAudit
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l) :
    audit.FLZModCuspLabelTargetAverageReductionAudit l :=
  { theta_source := part.theta_source,
    ind12_equality_part := part.ind12_equality_part,
    targetSigned_le_thetaAverage := part.targetSigned_le_thetaAverage }

theorem qSigned_le_thetaSourceAverage
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.qSigned <= part.theta_source.thetaSourceAverage audited :=
  part.toTargetAverageReductionAudit.qSigned_le_thetaSourceAverage audited

theorem qSigned_le_thetaSigned_via_average
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.qSigned <= package.preLedger.thetaSigned :=
  part.toTargetAverageReductionAudit.toQThetaComparisonAudit_qSigned_le_thetaSigned
    audited

theorem targetSigned_le_thetaSigned_via_average
    (part : audit.FLZModCuspLabelThetaContainerBoundAudit l)
    (audited : IUTStage1PlaceAuditedDirectSummandPacketChoice coric kind) :
    package.preLedger.targetVolume.targetSigned <= package.preLedger.thetaSigned :=
  part.toTargetAverageReductionAudit.targetSigned_le_thetaSigned_via_average
    audited

end FLZModCuspLabelThetaContainerBoundAudit

end LogVolumeChartAudit

end PlaceAuditedMultiradialThetaHullEndpoint

end IUTStage1SourcePackage

end Stage1
end Iut
