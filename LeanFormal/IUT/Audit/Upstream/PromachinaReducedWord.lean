import LeanFormal.IUT.Audit.Status
import Iut.Foundations.SourceReducedWordFiniteSeparation

/-!
  Audit metadata for the mechanically imported promachina reduced-word kernel.
  The imported source keeps its original `Iut` namespace and attribution.
-/

namespace LeanFormal.IUT.Audit

def promachinaReducedWordFiniteSeparation : Obligation :=
  { id := "Foundations.Anabelian.reduced-word-finite-separation"
    source :=
      "promachina/iut-lean 0d52e0fd, SourceReducedWordFiniteSeparation; Apache-2.0"
    status := VerificationStatus.proved
    note :=
      "A nonempty reduced word is separated by an explicit finite permutation " ++
        "representation. Residual finiteness is proved for free groups and " ++
        "transported to groups with an IsFreeGroup basis. Its dependency " ++
        "closure was copied mechanically under the original Iut module names, " ++
        "then changed only at documented Mathlib " ++
        "4.32.2 quotient-membership API boundary. This is not yet a tempered " ++
        "fundamental group or an IUT comparison theorem."
    dependsOn := [] }

end LeanFormal.IUT.Audit
