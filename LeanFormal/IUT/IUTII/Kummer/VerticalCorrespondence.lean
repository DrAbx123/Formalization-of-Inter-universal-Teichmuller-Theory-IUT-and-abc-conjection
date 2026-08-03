import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def verticalKummerCorrespondence : Obligation :=
  { id := "IUT-II.vertical-log-kummer"
    source := "IUT II, Sections 5-6"
    status := VerificationStatus.pending
    note :=
      "The lower polynomial/root kernel is available through the formal " ++
        "AdjoinRoot root and its algebraic-closure realization. The paper's " ++
        "vertical log-Kummer correspondence, its Frobenioid input, and all " ++
        "compatibility laws are still pending."
    dependsOn :=
      [ "IUT-I-II.prime-strips-frobenioids",
        "IUT-I-II.local-f-prime-strip-carrier",
        "IUT-II.kummer-polynomial-kernel",
        "IUT-II.adjoin-root-local-embedding",
        "IUT-II.vertical-log-kummer-correspondence",
        "IUT-I.initial-theta-data" ] }

end LeanFormal.IUT.Audit
