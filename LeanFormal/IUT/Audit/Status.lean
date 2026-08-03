/-! Machine-readable status vocabulary for the IUT audit ledger. -/

namespace LeanFormal.IUT.Audit

inductive VerificationStatus
  | proved
  | interface
  | externalAxiom
  | sorryPlaceholder
  | pending
  deriving DecidableEq, Repr

structure Obligation where
  id : String
  source : String
  status : VerificationStatus
  note : String
  /-- Lower-layer obligations that this module is allowed to use. -/
  dependsOn : List String := []
  /-- Non-constructive axioms explicitly accepted by this module. -/
  externalAxioms : List String := []
  /-- Named unfinished declarations; this is separate from `status`. -/
  sorryItems : List String := []
  deriving Repr

end LeanFormal.IUT.Audit
