import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.Foundations.Arithmetic.PrimeIntervals
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
  Concrete local carriers for the lower part of an IUT prime strip.

  For a rational prime `p`, the local field is Mathlib's `ℚ_[p]` and the
  local Galois group is the group of algebraic-closure automorphisms over that
  field.  The D-strip below uses this actual group on both sides of the
  projection.  This is intentionally a carrier construction only: the
  geometric fundamental group, the etale quotient, integral monoids, and the
  arithmetic Frobenius data of the paper are still separate obligations.
-/

namespace LeanFormal.IUT

abbrev RationalPrimePlace : Type := {p : Nat // Nat.Prime p}

abbrev FinitePrimePlace (lower upper : Nat) : Type :=
  {p : Nat // p ∈ primeStrip lower upper}

noncomputable instance finitePrimePlaceFintype (lower upper : Nat) :
    Fintype (FinitePrimePlace lower upper) :=
  (primeStrip_finite lower upper).fintype

def FinitePrimePlace.toRationalPrimePlace
    {lower upper : Nat} (v : FinitePrimePlace lower upper) : RationalPrimePlace :=
  ⟨v.1, v.2.2.2⟩

theorem FinitePrimePlace.prime
    {lower upper : Nat} (v : FinitePrimePlace lower upper) : Nat.Prime v.1 :=
  v.2.2.2

abbrev LocalAbsoluteGalois (p : Nat) [Fact (Nat.Prime p)] : Type :=
  AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]

noncomputable def localGaloisUnitsAction (p : Nat) [Fact (Nat.Prime p)] :
    LocalAbsoluteGalois p →* MulAut (AlgebraicClosure ℚ_[p])ˣ where
  toFun σ := Units.mapEquiv σ.toRingEquiv.toMulEquiv
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl

noncomputable def localDPrimeStrip : DPrimeStrip RationalPrimePlace where
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

noncomputable def finiteLocalDPrimeStrip (lower upper : Nat) :
    DPrimeStrip (FinitePrimePlace lower upper) where
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

noncomputable def localQParameterFor (p : Nat) [Fact (Nat.Prime p)] :
    (AlgebraicClosure ℚ_[p])ˣ :=
  Units.mk0 (p : AlgebraicClosure ℚ_[p])
    (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))

noncomputable def localQParameter (v : RationalPrimePlace) := by
  letI := Fact.mk v.2
  exact localQParameterFor v.1

theorem localQParameter_ne_one (v : RationalPrimePlace) :
    localQParameter v ≠ 1 := by
  letI := Fact.mk v.2
  intro h
  haveI : CharZero (AlgebraicClosure ℚ_[v.1]) :=
    charZero_of_injective_algebraMap
      (algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1])).injective
  have hv := congrArg Units.val h
  change (v.1 : AlgebraicClosure ℚ_[v.1]) = 1 at hv
  exact v.2.ne_one (Nat.cast_injective hv)

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localPrimePlaceCarrier : Obligation :=
  { id := "IUT-I-II.local-prime-place-carrier"
    source := "IUT I, Definition 5.2; IUT II, local prime-strip input"
    status := VerificationStatus.proved
    note :=
      "Rational prime labels, local p-adic fields, absolute Galois groups, " ++
        "their action on local units, and a nontrivial local q-parameter are " ++
        "constructed with Mathlib. This is only the carrier layer; etale " ++
        "fundamental-group and Frobenioid realization remain pending."
    dependsOn := [ "IUT-I-II.prime-strip-core" ] }

end LeanFormal.IUT.Audit
