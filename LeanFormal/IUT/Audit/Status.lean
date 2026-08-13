/-! Machine-readable status vocabulary for the IUT audit ledger. -/

namespace LeanFormal.IUT.Audit

inductive VerificationStatus
  /-- A theorem whose statement and proof are source-faithful to the cited paper. -/
  | proved
  /-- A proved ordinary algebraic/logical kernel with no source realization. -/
  | provedKernel
  /-- A proved projection from an explicitly supplied source object. -/
  | sourceProjection
  /-- A proved theorem for a concrete or finite test carrier only. -/
  | testCarrier
  /-- A theorem proved from explicit source-facing fields, still conditional. -/
  | conditional
  | interface
  | externalAxiom
  | sorryPlaceholder
  | pending
  deriving DecidableEq, Repr

namespace VerificationStatus

/-- Only this status may be used for a complete source-faithful theorem. -/
def isSourceFaithful : VerificationStatus → Bool
  | .proved => true
  | _ => false

/-- These statuses document proved mathematics without claiming the paper's
    source carrier or quantifier boundary. -/
def isProvedNonSource : VerificationStatus → Bool
  | .provedKernel | .sourceProjection | .testCarrier | .conditional => true
  | _ => false

/-- A completed paper input recognition result is not made pending by an
    optional foundations-to-input construction route. -/
def isCompletedStage : VerificationStatus → Bool
  | .proved | .provedKernel | .sourceProjection | .testCarrier | .conditional => true
  | _ => false

end VerificationStatus

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
