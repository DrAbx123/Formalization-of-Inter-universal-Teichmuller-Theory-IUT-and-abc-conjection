import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def theorem311Output : Obligation :=
  { id := "IUT-III.theorem-3.11-output"
    source := "IUT III, Theorem 3.11"
    status := VerificationStatus.pending
    note := "Construct the multiradial output over the actual IUT I-II data."
    dependsOn := ["IUT-I.initial-theta-data", "IUT-I-II.prime-strips-frobenioids", "IUT-II.vertical-log-kummer"] }

end LeanFormal.IUT.Audit
