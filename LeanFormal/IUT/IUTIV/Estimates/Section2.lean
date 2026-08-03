import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def iutIVSection2 : Obligation :=
  { id := "IUT-IV.section-2"
    source := "IUT IV, Section 2"
    status := VerificationStatus.pending
    note := "The explicit estimates remain downstream of Corollary 3.12." }

end LeanFormal.IUT.Audit
