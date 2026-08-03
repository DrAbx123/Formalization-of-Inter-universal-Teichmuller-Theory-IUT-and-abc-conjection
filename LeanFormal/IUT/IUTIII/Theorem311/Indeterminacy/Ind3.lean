import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def ind3 : Obligation :=
  { id := "IUT-III.Ind3"
    source := "IUT III, Theorem 3.11 (Ind3)"
    status := VerificationStatus.pending
    note := "Construct and prove upper-semi compatibility, not just state it."
    dependsOn := ["IUT-II.vertical-log-kummer", "IUT-III.generic-quotient-transport", "IUT-III.Ind3.upper-semi-kernel"] }

end LeanFormal.IUT.Audit
