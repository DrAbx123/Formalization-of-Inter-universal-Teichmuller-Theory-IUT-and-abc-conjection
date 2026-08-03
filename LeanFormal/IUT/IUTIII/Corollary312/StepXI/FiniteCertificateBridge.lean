import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.Audit.Status

/-!
  Explicit bridge from the finite arithmetic certificate to the Step-XI
  contract.

  The bridge deliberately requires the source-facing link data as fields:
  `targetSigned`, IPL/SHE/APT evidence, and the two comparison inequalities.
  Therefore this file proves only the assembly of a supplied certificate; it
  does not manufacture any IUT object or discharge the disputed compatibility.
-/

namespace LeanFormal.IUT

structure FiniteStepXILinkEvidence {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) where
  targetSigned : Real
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt
  q_le_target : certificate.qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ certificate.thetaSigned

def StepXIFiniteCertificate.toContract {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (links : FiniteStepXILinkEvidence certificate) : StepXIContract :=
  { qSigned := certificate.qSigned
    thetaSigned := certificate.thetaSigned
    targetSigned := links.targetSigned
    q_negative := certificate.q_negative
    ipl := links.ipl
    she := links.she
    apt := links.apt
    ipl_evidence := links.ipl_evidence
    she_evidence := links.she_evidence
    apt_evidence := links.apt_evidence
    q_le_target := links.q_le_target
    target_le_theta := links.target_le_theta }

theorem cor312_of_finite_certificate
    {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (links : FiniteStepXILinkEvidence certificate) :
    Cor312Conclusion (certificate.toContract links) := by
  exact cor312_of_constructed_stepXI (certificate.toContract links)

theorem q_positive_of_finite_certificate
    {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (links : FiniteStepXILinkEvidence certificate) :
    0 < -(certificate.toContract links).qSigned := by
  exact q_positive_of_constructed_stepXI (certificate.toContract links)

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finiteCertificateBridge : Obligation :=
  { id := "IUT-III.finite-certificate-to-contract"
    source := "IUT III Corollary 3.12, Step (xi)"
    status := VerificationStatus.interface
    note :=
      "Contract assembly is proved once explicit target, IPL/SHE/APT evidence, " ++
        "and comparison bounds are supplied; source-facing construction of those " ++
        "fields remains pending." }

end LeanFormal.IUT.Audit
