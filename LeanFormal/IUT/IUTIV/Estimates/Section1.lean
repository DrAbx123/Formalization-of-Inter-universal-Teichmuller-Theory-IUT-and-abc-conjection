import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def iutIVSection1 : Obligation :=
  { id := "IUT-IV.section-1"
    source := "IUT IV, Section 1"
    status := VerificationStatus.pending
    note := "Import elementary estimates only after the Corollary 3.12 dependency is explicit." }

end LeanFormal.IUT.Audit
