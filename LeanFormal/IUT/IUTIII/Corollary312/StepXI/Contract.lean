import LeanFormal.IUT.Audit.Status
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
  The explicit proof boundary at IUT III, Theorem 3.11 -> Corollary 3.12.

  The structures here are *contracts for obligations*, not definitions of the
  paper's Hodge theaters, Frobenioids, prime strips, or Kummer maps.  The
  source-facing construction must eventually replace each proposition by a
  construction from those standard objects.

  The source-facing existence of a package satisfying the paper's Step-(xi)
  requirements is intentionally not declared here.  The ordered-real
  conclusion below is available only after an explicit contract is supplied.
-/

namespace LeanFormal.IUT

inductive WallObligation
  | ind1
  | ind2
  | ind3
  | ipl
  | she
  | apt
  | holomorphicHull
  | determinantNormalization
  | logVolumeComparison
  deriving DecidableEq, Repr

structure StepXIContract where
  qSigned : Real
  thetaSigned : Real
  targetSigned : Real
  q_negative : qSigned < 0
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt
  q_le_target : qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ thetaSigned

def Cor312Conclusion (contract : StepXIContract) : Prop :=
  contract.qSigned ≤ contract.thetaSigned

theorem cor312_of_constructed_stepXI (contract : StepXIContract) :
    Cor312Conclusion contract := by
  exact le_trans contract.q_le_target contract.target_le_theta

theorem q_positive_of_constructed_stepXI (contract : StepXIContract) :
    0 < -contract.qSigned := by
  exact neg_pos.mpr contract.q_negative

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def stepXIContractConstruction : Obligation :=
  { id := "IUT-III.StepXI.contract-construction"
    source := "IUT III, Theorem 3.11 -> Corollary 3.12, Steps (xi-a)-(xi-g)"
    status := VerificationStatus.pending
    note :=
      "The ordered conclusion is proved from a contract; construction of the " ++
      "contract from IUT source data is unfinished; no placeholder theorem is " ++
      "exported in the production namespace."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output",
        "IUT-III.Ind1",
        "IUT-III.Ind2",
        "IUT-III.Ind3",
        "IUT-III.IPL",
        "IUT-III.SHE",
        "IUT-III.APT",
        "IUT-III.holomorphic-hull-determinant-log-volume" ]
    sorryItems := [] }

end LeanFormal.IUT.Audit
