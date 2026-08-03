import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def initialThetaData : Obligation :=
  { id := "IUT-I.initial-theta-data"
    source := "IUT I, Sections 3-4"
    status := VerificationStatus.pending
    note := "Construct the initial Theta data from the number field and elliptic curve; the arithmetic/curve input record is now explicit, but existence and the remaining geometric conditions are pending."
    dependsOn := ["IUT-I.initial-theta-arithmetic-data"] }

def hodgeTheaterHistories : Obligation :=
  { id := "IUT-I.hodge-theater-histories"
    source := "IUT I, Sections 4-5"
    status := VerificationStatus.pending
    note := "Construct distinct histories and their links; do not use an unconstrained record." }

end LeanFormal.IUT.Audit
