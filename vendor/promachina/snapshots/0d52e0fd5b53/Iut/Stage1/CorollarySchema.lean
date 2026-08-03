/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.AlgorithmicBridge
import Iut.Stage1.PilotComparison
import Mathlib.Tactic

/-!
Stage 1 schema for the Corollary 3.12 signed real inequality.

The display near the end of IUT III, Corollary 3.12 compares signed real
log-volume values such as `-|log(q)| <= -|log(Theta)|`. The existing
`PilotLogVolume.value` stores the corresponding positive magnitude. This file
keeps the sign conversion explicit.
-/

namespace Iut
namespace Stage1

open RealLineCopy

/--
Turn a signed real log-volume, such as `-|log(q)|`, into a tagged pilot
log-volume whose stored value is the positive magnitude.
-/
def signedPilotLogVolume (side : PilotSide) (signedValue : Real) : PilotLogVolume :=
  { side := side, value := -signedValue }

@[simp]
theorem signedPilotLogVolume_side (side : PilotSide) (signedValue : Real) :
    (signedPilotLogVolume side signedValue).side = side :=
  rfl

@[simp]
theorem signedPilotLogVolume_value (side : PilotSide) (signedValue : Real) :
    (signedPilotLogVolume side signedValue).value = -signedValue :=
  rfl

theorem corollary312_of_signed_le {thetaSigned qSigned : Real}
    (hle : qSigned <= thetaSigned) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta thetaSigned)
      (signedPilotLogVolume PilotSide.q qSigned) := by
  unfold Corollary312Inequality signedPilotLogVolume
  linarith

/--
Abstract signed comparison payload for the Corollary 3.12 endpoint.

This record isolates the real-valued comparison data from any particular toy
model, bridge construction, or source-obligation ledger.
-/
structure Corollary312ComparisonData where
  thetaSigned : Real
  qSigned : Real
  q_positive : 0 < -qSigned
  qSigned_le_thetaSigned : qSigned <= thetaSigned

namespace Corollary312ComparisonData

def thetaPilot (data : Corollary312ComparisonData) : PilotLogVolume :=
  signedPilotLogVolume PilotSide.theta data.thetaSigned

def qPilot (data : Corollary312ComparisonData) : PilotLogVolume :=
  signedPilotLogVolume PilotSide.q data.qSigned

theorem thetaPilot_side (data : Corollary312ComparisonData) :
    data.thetaPilot.side = PilotSide.theta :=
  rfl

theorem qPilot_side (data : Corollary312ComparisonData) :
    data.qPilot.side = PilotSide.q :=
  rfl

theorem qPilot_positive (data : Corollary312ComparisonData) :
    0 < data.qPilot.value := by
  simpa [qPilot, signedPilotLogVolume] using data.q_positive

theorem corollary312 (data : Corollary312ComparisonData) :
    Corollary312Inequality data.thetaPilot data.qPilot :=
  corollary312_of_signed_le data.qSigned_le_thetaSigned

def stage1Comparison (data : Corollary312ComparisonData) :
    Stage1Comparison :=
  { theta := data.thetaPilot,
    q := data.qPilot,
    theta_side := data.thetaPilot_side,
    q_side := data.qPilot_side,
    q_positive := data.qPilot_positive,
    comparison := data.corollary312 }

theorem stage1Comparison_comparison_eq_corollary312
    (data : Corollary312ComparisonData) :
    data.stage1Comparison.comparison = data.corollary312 :=
  rfl

theorem stage1Comparison_recovers_corollary312
    (data : Corollary312ComparisonData) :
    corollary312_from_stage1_comparison data.stage1Comparison =
      data.corollary312 :=
  rfl

def publicAudit (data : Corollary312ComparisonData) :
    data.qSigned <= data.thetaSigned ∧
      Corollary312Inequality data.thetaPilot data.qPilot ∧
      corollary312_from_stage1_comparison data.stage1Comparison =
        corollary312_of_signed_le data.qSigned_le_thetaSigned :=
  ⟨data.qSigned_le_thetaSigned, data.corollary312, rfl⟩

theorem publicAudit_qSigned_le_thetaSigned
    (data : Corollary312ComparisonData) :
    data.qSigned <= data.thetaSigned :=
  data.publicAudit.1

theorem publicAudit_corollary312
    (data : Corollary312ComparisonData) :
    Corollary312Inequality data.thetaPilot data.qPilot :=
  data.publicAudit.2.1

theorem publicAudit_stage1Comparison_recovers
    (data : Corollary312ComparisonData) :
    corollary312_from_stage1_comparison data.stage1Comparison =
      corollary312_of_signed_le data.qSigned_le_thetaSigned :=
  data.publicAudit.2.2

end Corollary312ComparisonData

def stage1Comparison_of_signed_le {thetaSigned qSigned : Real}
    (hq_positive : 0 < -qSigned) (hle : qSigned <= thetaSigned) :
    Stage1Comparison :=
  let data : Corollary312ComparisonData :=
    { thetaSigned := thetaSigned,
      qSigned := qSigned,
      q_positive := hq_positive,
      qSigned_le_thetaSigned := hle }
  data.stage1Comparison

theorem corollary312_from_bridge
    {source target : Copy} {index : Type u}
    {output : AlgorithmicOutput source target index}
    {measure : RegionMeasure target} {thetaSigned qSigned : Real}
    (bridge : output.CommonTargetBoundBridge measure thetaSigned)
    (certified : output.Certified) (choice : index)
    (hq_le_choice :
      qSigned <= RegionMeasure.targetVolume measure (output.comparison choice)) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta thetaSigned)
      (signedPilotLogVolume PilotSide.q qSigned) := by
  exact corollary312_of_signed_le
    (le_trans hq_le_choice (bridge.choice_targetVolume_le certified choice))

theorem corollary312_from_structured_bridge
    {source target : Copy} {index : Type u}
    {output : AlgorithmicOutput source target index}
    {measure : RegionMeasure target} {thetaSigned qSigned : Real}
    (bridge : output.StructuredCommonTargetBoundBridge measure thetaSigned)
    (certificate : QualitativeData.StructuredCertificate output.family)
    (choice : index)
    (hq_le_choice :
      qSigned <= RegionMeasure.targetVolume measure (output.comparison choice)) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta thetaSigned)
      (signedPilotLogVolume PilotSide.q qSigned) := by
  exact corollary312_of_signed_le
    (le_trans hq_le_choice (bridge.choice_targetVolume_le certificate choice))

def stage1Comparison_from_bridge
    {source target : Copy} {index : Type u}
    {output : AlgorithmicOutput source target index}
    {measure : RegionMeasure target} {thetaSigned qSigned : Real}
    (bridge : output.CommonTargetBoundBridge measure thetaSigned)
    (certified : output.Certified) (choice : index)
    (hq_positive : 0 < -qSigned)
    (hq_le_choice :
      qSigned <= RegionMeasure.targetVolume measure (output.comparison choice)) :
    Stage1Comparison :=
  stage1Comparison_of_signed_le hq_positive
    (le_trans hq_le_choice (bridge.choice_targetVolume_le certified choice))

def stage1Comparison_from_structured_bridge
    {source target : Copy} {index : Type u}
    {output : AlgorithmicOutput source target index}
    {measure : RegionMeasure target} {thetaSigned qSigned : Real}
    (bridge : output.StructuredCommonTargetBoundBridge measure thetaSigned)
    (certificate : QualitativeData.StructuredCertificate output.family)
    (choice : index)
    (hq_positive : 0 < -qSigned)
    (hq_le_choice :
      qSigned <= RegionMeasure.targetVolume measure (output.comparison choice)) :
    Stage1Comparison :=
  stage1Comparison_of_signed_le hq_positive
    (le_trans hq_le_choice (bridge.choice_targetVolume_le certificate choice))

end Stage1
end Iut
