import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def frobenioidPrimeStrips : Obligation :=
  { id := "IUT-I-II.prime-strips-frobenioids"
    source := "IUT I, Sections 5-6; Geometry of Frobenioids I-II"
    status := VerificationStatus.pending
    note := "Construct the prime strips and Frobenioid links from lower-layer objects; the carrier and degree kernels are proved separately."
    dependsOn :=
      [ "IUT-I-II.prime-strip-core",
        "IUT-I-II.prime-strip-degree-kernel",
        "IUT-I-II.local-prime-place-carrier",
        "IUT-I-II.local-f-prime-strip-carrier" ] }

end LeanFormal.IUT.Audit
