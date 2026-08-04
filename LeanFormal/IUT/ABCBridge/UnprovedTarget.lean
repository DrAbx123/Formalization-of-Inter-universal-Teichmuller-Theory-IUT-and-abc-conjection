import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.Audit.Status

/-!
  Explicit proof boundary for the ABC conjecture.

  `ABCConjecture` is a standard arithmetic proposition defined in `ABC.lean`.
  This module records the missing proof as an audit obligation; it deliberately
  does not manufacture a theorem whose body is `sorry`.
-/

namespace LeanFormal.IUT.Audit

def abcConjectureProofTarget : Obligation :=
  { id := "ABC.proof-target"
    source := "Standard integer ABC conjecture"
    status := VerificationStatus.pending
    note := "The standard proposition is stated, but its global epsilon proof is not supplied."
    dependsOn := [ "ABC.statement" ] }

end LeanFormal.IUT.Audit
