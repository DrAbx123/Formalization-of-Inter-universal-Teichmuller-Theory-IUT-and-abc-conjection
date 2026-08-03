/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.SourceObligations

/-!
Non-toy scaffold for future IUT-specific Stage 1 source data.

This module does not assert that the IUT hypotheses have been supplied. It gives
future source-specific work a small interface: produce a `SourceObligationLedger`,
then the shared audit and public Stage 1 endpoints follow from the common API.
-/

namespace Iut
namespace Stage1

open RealLineCopy

/--
A provider of the source obligations required by the Stage 1 public endpoint.

Future IUT-specific modules should construct the `ledger` field from actual
formalized IPL, SHE, chart, membership, common-bound, and normalization data.
-/
structure IUTSourceObligationProvider
    {source target : Copy} {index : Type u}
    (output : AlgorithmicOutput source target index)
    (measure : RegionMeasure target) (thetaSigned qSigned : Real)
    (normalization : Prop) where
  ledger : SourceObligationLedger output measure thetaSigned qSigned normalization

namespace IUTSourceObligationProvider

variable {source target : Copy} {index : Type u}
variable {output : AlgorithmicOutput source target index}
variable {measure : RegionMeasure target}
variable {thetaSigned qSigned : Real}
variable {normalization : Prop}

def audit (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    SourceObligationLedger.Audit provider.ledger :=
  provider.ledger.audit

theorem qSigned_le_thetaSigned (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    qSigned <= thetaSigned :=
  provider.ledger.qSigned_le_thetaSigned

theorem corollary312 (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta thetaSigned)
      (signedPilotLogVolume PilotSide.q qSigned) :=
  provider.ledger.corollary312

def comparisonData (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    Corollary312ComparisonData :=
  provider.ledger.comparisonData

theorem comparisonData_corollary312_eq (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    provider.comparisonData.corollary312 = provider.corollary312 :=
  rfl

def stage1Comparison (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    Stage1Comparison :=
  provider.ledger.stage1Comparison

theorem comparisonData_stage1Comparison_eq (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    provider.comparisonData.stage1Comparison = provider.stage1Comparison :=
  rfl

theorem publicAudit (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    qSigned <= thetaSigned ∧
      Corollary312Inequality
        (signedPilotLogVolume PilotSide.theta thetaSigned)
        (signedPilotLogVolume PilotSide.q qSigned) ∧
      (corollary312_from_stage1_comparison provider.stage1Comparison =
        corollary312_of_signed_le provider.ledger.qSigned_le_thetaSigned) := by
  let publicAudit := provider.ledger.publicAudit
  exact ⟨publicAudit.1, publicAudit.2.1, by
    change corollary312_from_stage1_comparison provider.ledger.stage1Comparison =
      corollary312_of_signed_le provider.ledger.qSigned_le_thetaSigned
    exact publicAudit.2.2⟩

theorem stage1Comparison_recovers_corollary312 (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    corollary312_from_stage1_comparison provider.stage1Comparison =
      provider.ledger.corollary312 :=
  rfl

theorem hasNormalization (provider :
    IUTSourceObligationProvider output measure thetaSigned qSigned normalization) :
    normalization :=
  provider.ledger.normalization_proof

end IUTSourceObligationProvider

end Stage1
end Iut
