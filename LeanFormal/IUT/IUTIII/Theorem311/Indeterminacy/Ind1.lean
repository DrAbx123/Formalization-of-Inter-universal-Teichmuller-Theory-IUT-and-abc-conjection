import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def ind1 : Obligation :=
  { id := "IUT-III.Ind1"
    source := "IUT III, Theorem 3.11 (Ind1)"
    status := VerificationStatus.pending
    note := "Prove the first quotient compatibility from the constructed output."
    dependsOn := ["IUT-I-II.prime-strip-core", "IUT-III.generic-quotient-transport", "IUT-III.orbit-quotient-transport"] }

end LeanFormal.IUT.Audit
