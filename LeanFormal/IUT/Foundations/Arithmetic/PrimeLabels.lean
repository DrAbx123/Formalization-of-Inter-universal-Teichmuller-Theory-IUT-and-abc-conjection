import LeanFormal.IUT.Audit.Status
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
  The ordinary prime label `l ≥ 5` used throughout the finite theta kernels.

  This is a foundation-level arithmetic record.  It is not the initial
  Theta-data existence theorem from IUT I.
-/

namespace LeanFormal.IUT

structure PrimeGeFive where
  value : Nat
  prime : Nat.Prime value
  ge_five : 5 ≤ value

namespace PrimeGeFive

instance (l : PrimeGeFive) : NeZero l.value :=
  ⟨l.prime.ne_zero⟩

theorem ne_two (l : PrimeGeFive) : l.value ≠ 2 := by
  intro h
  have h5 := l.ge_five
  omega

theorem odd (l : PrimeGeFive) : Odd l.value := by
  exact l.prime.odd_of_ne_two (ne_two l)

theorem factPrime (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  ⟨l.prime⟩

end PrimeGeFive

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def primeLabelArithmetic : Obligation :=
  { id := "Foundations.Arithmetic.prime-label-ge-five"
    source := "IUT I, Definition 3.1 (prime label condition)"
    status := VerificationStatus.proved
    note :=
      "The explicit prime-at-least-five record and its oddness/Fact instances " ++
        "are proved. Initial Theta-data existence is a separate interface."
    dependsOn := [] }

end LeanFormal.IUT.Audit
