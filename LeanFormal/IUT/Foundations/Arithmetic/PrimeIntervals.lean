import LeanFormal.IUT.Audit.Status
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
  Finite prime-index arithmetic.

  The set below is only the ordinary finite set of primes in an interval.  It
  is deliberately not the Frobenioid prime-strip object of IUT I--II.
-/

namespace LeanFormal.IUT

def primeStrip (lower upper : Nat) : Set Nat :=
  {p | lower ≤ p ∧ p ≤ upper ∧ Nat.Prime p}

theorem mem_primeStrip_iff {lower upper p : Nat} :
    p ∈ primeStrip lower upper ↔
      lower ≤ p ∧ p ≤ upper ∧ Nat.Prime p :=
  Iff.rfl

theorem primeStrip_finite (lower upper : Nat) :
    (primeStrip lower upper).Finite := by
  refine (Set.finite_Icc lower upper).subset ?_
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

theorem primeStrip_isPrime {lower upper p : Nat}
    (hp : p ∈ primeStrip lower upper) : Nat.Prime p :=
  hp.2.2

theorem primeStrip_subset_of_interval
    {lower₁ upper₁ lower₂ upper₂ : Nat}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂) :
    primeStrip lower₁ upper₁ ⊆ primeStrip lower₂ upper₂ := by
  intro p hp
  exact ⟨hlower.trans hp.1, hp.2.1.trans hupper, hp.2.2⟩

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def primeIntervalArithmetic : Obligation :=
  { id := "Foundations.Arithmetic.prime-intervals"
    source := "Standard finite prime-index arithmetic"
    status := VerificationStatus.proved
    note :=
      "Finite interval prime sets, primality projection, and interval inclusion " ++
        "are proved; no Frobenioid structure is asserted."
    dependsOn := [] }

end LeanFormal.IUT.Audit
