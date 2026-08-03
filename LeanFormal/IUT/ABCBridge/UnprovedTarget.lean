import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.Audit.Status

/-!
  Explicit proof boundary for the ABC conjecture.

  `ABCConjecture` is a standard arithmetic proposition defined in `ABC.lean`.
  The theorem below is intentionally an unfinished target.  Its `sorry` is
  the only reason Lean accepts the assertion; it is not evidence that ABC has
  been proved.
-/

namespace LeanFormal.IUT

theorem abc_conjecture_target : ABCConjecture := by
  sorry

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def abcConjectureProofTarget : Obligation :=
  { id := "ABC.proof-target"
    source := "Standard integer ABC conjecture"
    status := VerificationStatus.sorryPlaceholder
    note := "The standard proposition is stated, but its global epsilon proof is not supplied."
    dependsOn := [ "ABC.statement" ]
    sorryItems := [ "LeanFormal.IUT.abc_conjecture_target" ] }

end LeanFormal.IUT.Audit
