import LeanFormal.IUT.Foundations.Arithmetic.PrimeIntervals
import LeanFormal.IUT.Audit.Status

/-!
  IUT II source boundary for prime-strip arithmetic.

  The ordinary finite interval facts are imported from the foundation layer;
  this file records that the paper's Frobenioid realization is a separate
  obligation and is not identified with the set `primeStrip`.
-/

namespace LeanFormal.IUT.Audit

def primeStripArithmetic : Obligation :=
  { id := "IUT-I-II.prime-strip-finite-arithmetic"
    source := "IUT I--II prime-strip prerequisites"
    status := VerificationStatus.proved
    note :=
      "Finite interval prime-index facts are proved in the foundation layer; " ++
        "the Frobenioid prime strips and their links remain pending."
    dependsOn := [ "Foundations.Arithmetic.prime-intervals" ] }

end LeanFormal.IUT.Audit
