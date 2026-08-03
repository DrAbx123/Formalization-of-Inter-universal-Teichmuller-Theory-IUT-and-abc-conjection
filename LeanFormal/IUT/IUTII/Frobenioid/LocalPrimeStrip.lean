import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.Foundations.Arithmetic.NormLog
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Padics.Complex

/-!
  A concrete local-value realization of the `FPrimeStrip` carrier.

  The value monoid is the multiplicative group of units in the algebraic
  closure of `ℚ_[p]`.  Its real-valued degree is the ambient p-adic norm.  The
  norm is multiplicative in Mathlib, so the degree is an official `MonoidHom`;
  no replacement valuation or ad hoc degree law is introduced here.  This is
  still below the Frobenioid layer: integral models, arithmetic Frobenius, and
  the etale quotient are separate obligations.
-/

namespace LeanFormal.IUT

noncomputable abbrev localUnitNormDegreeFor (p : Nat) [Fact (Nat.Prime p)] :
    (AlgebraicClosure ℚ_[p])ˣ →* Multiplicative Real :=
  unitNormLogDegree (AlgebraicClosure ℚ_[p])

theorem localUnitNormDegreeFor_apply_mul
    (p : Nat) [Fact (Nat.Prime p)]
    (u v : (AlgebraicClosure ℚ_[p])ˣ) :
    localUnitNormDegreeFor p (u * v) =
      localUnitNormDegreeFor p u * localUnitNormDegreeFor p v := by
  exact (localUnitNormDegreeFor p).map_mul u v

noncomputable def localFPrimeStrip : FPrimeStrip RationalPrimePlace where
  Pi := fun v => letI := Fact.mk v.2; LocalAbsoluteGalois v.1
  groupPi := fun v => by
    letI := Fact.mk v.2
    exact inferInstanceAs (Group (LocalAbsoluteGalois v.1))
  G := fun v => letI := Fact.mk v.2; LocalAbsoluteGalois v.1
  groupG := fun v => by
    letI := Fact.mk v.2
    exact inferInstanceAs (Group (LocalAbsoluteGalois v.1))
  proj := fun v => MonoidHom.id _
  proj_surjective := fun _ => Function.surjective_id
  Mon := fun v => letI := Fact.mk v.2; (AlgebraicClosure ℚ_[v.1])ˣ
  commMonoidMon := fun v => by
    letI := Fact.mk v.2
    infer_instance
  action := fun v => by
    letI := Fact.mk v.2
    exact localGaloisUnitsAction v.1
  degree := fun v => by
    letI := Fact.mk v.2
    exact localUnitNormDegreeFor v.1

noncomputable def finiteLocalFPrimeStrip (lower upper : Nat) :
    FPrimeStrip (FinitePrimePlace lower upper) where
  Pi := fun v =>
    letI := Fact.mk v.prime
    LocalAbsoluteGalois v.1
  groupPi := fun v => by
    letI := Fact.mk v.prime
    exact inferInstanceAs (Group (LocalAbsoluteGalois v.1))
  G := fun v =>
    letI := Fact.mk v.prime
    LocalAbsoluteGalois v.1
  groupG := fun v => by
    letI := Fact.mk v.prime
    exact inferInstanceAs (Group (LocalAbsoluteGalois v.1))
  proj := fun v => MonoidHom.id _
  proj_surjective := fun _ => Function.surjective_id
  Mon := fun v =>
    letI := Fact.mk v.prime
    (AlgebraicClosure ℚ_[v.1])ˣ
  commMonoidMon := fun v => by
    letI := Fact.mk v.prime
    infer_instance
  action := fun v => by
    letI := Fact.mk v.prime
    exact localGaloisUnitsAction v.1
  degree := fun v => by
    letI := Fact.mk v.prime
    exact localUnitNormDegreeFor v.1

theorem localFPrimeStrip_degree_mul
    (v : RationalPrimePlace)
    (u w : localFPrimeStrip.Mon v) :
    localFPrimeStrip.degree v (u * w) =
      localFPrimeStrip.degree v u * localFPrimeStrip.degree v w := by
  letI := Fact.mk v.2
  exact (localUnitNormDegreeFor v.1).map_mul u w

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localFPrimeStripCarrier : Obligation :=
  { id := "IUT-I-II.local-f-prime-strip-carrier"
    source := "IUT I, Definition 5.2; IUT II, prime-strip value monoids"
    status := VerificationStatus.interface
    note :=
      "Local units of algebraic closures of p-adic fields, Galois actions, " ++
        "and norm-valued degree maps form concrete F-prime-strip carriers. " ++
        "Integral Frobenioid, arithmetic Frobenius, and etale realization remain pending."
    dependsOn :=
      [ "IUT-I-II.prime-strip-core", "IUT-I-II.local-prime-place-carrier" ] }

end LeanFormal.IUT.Audit
