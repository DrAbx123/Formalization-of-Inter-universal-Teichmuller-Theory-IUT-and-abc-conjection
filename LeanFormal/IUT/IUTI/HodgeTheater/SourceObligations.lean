import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def hodgeTheaterSource : Obligation :=
  { id := "IUT-I.hodge-theater-source"
    source := "IUT I, Section 4"
    status := VerificationStatus.pending
    note := "The source construction must provide the arithmetic and geometric structures; the D/F prime-strip carrier kernel is proved separately."
    dependsOn :=
      [ "IUT-I-II.prime-strip-core",
        "IUT-I-II.local-prime-place-carrier",
        "IUT-I.initial-theta-data" ] }

end LeanFormal.IUT.Audit
