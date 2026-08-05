/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidPresentation

/-!
# Integral evaluation of the model Frobenioid

For the model Frobenioid of Frobenioids I, Theorem 5.2, the monoid
`O^triangle` at the zero-divisor object consists exactly of the rational
functions whose divisor is effective.  This is the carrier-level statement
used in IUT II, Definition 4.9(iii), before specializing effectiveness to a
local valuation-integrality condition.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid.Carrier

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : forall {X Y : D}, (X ⟶ Y) -> Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

private abbrev P := preFrobenioid (Phi := Phi) (data := data)

@[simp]
theorem zeroObject_divisorClass_eq_zero (base : D) :
    Object.divisorClass (zeroObject Phi data base) = 0 :=
  rfl

/-- Rational functions at a model object whose divisor is represented by an
effective divisor at the object's base. -/
def effectiveRationalFunctionSubmonoid (object : Carrier Phi data) :
    Submonoid
      (Multiplicative
        (data.rationalFunctions.obj (Object.base object))) where
  carrier value :=
    data.divisor (Object.base object) value.toAdd ∈
      Set.range
        (Algebra.GrothendieckAddGroup.of
          (M := (Phi.obj (Object.base object)).carrier))
  one_mem' := by
    refine ⟨0, ?_⟩
    simp
  mul_mem' := by
    intro first second firstEffective secondEffective
    rcases firstEffective with ⟨firstDivisor, firstDivisor_eq⟩
    rcases secondEffective with ⟨secondDivisor, secondDivisor_eq⟩
    refine ⟨firstDivisor + secondDivisor, ?_⟩
    change
      Algebra.GrothendieckAddGroup.of (firstDivisor + secondDivisor) =
        data.divisor (Object.base object) (first.toAdd + second.toAdd)
    rw [map_add, map_add, firstDivisor_eq, secondDivisor_eq]

/-- The balance equation for a linear base-identity endomorphism of the
zero-divisor object says precisely that its rational function is effective. -/
theorem zeroObject_endomorphism_balance
    (base : D)
    (endomorphism :
      P.LinearBaseIdentityEndomorphism (zeroObject Phi data base)) :
    Algebra.GrothendieckAddGroup.of endomorphism.hom.divisor =
      data.divisor (Object.base (zeroObject Phi data base))
        endomorphism.hom.rationalFunction := by
  exact endomorphism_divisor_eq Phi data endomorphism

/-- Forget the effective divisor and retain the rational-function coordinate
of an element of `O^triangle` at the zero-divisor object. -/
def zeroObjectRationalFunctionHom (base : D) :
    P.LinearBaseIdentityEndomorphism (zeroObject Phi data base) →*
      effectiveRationalFunctionSubmonoid
        (Phi := Phi) (data := data) (zeroObject Phi data base) where
  toFun endomorphism :=
    ⟨Multiplicative.ofAdd endomorphism.hom.rationalFunction,
      ⟨endomorphism.hom.divisor,
        zeroObject_endomorphism_balance
          (Phi := Phi) (data := data) base endomorphism⟩⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply Subtype.ext
    change Multiplicative.ofAdd (first * second).hom.rationalFunction =
      Multiplicative.ofAdd
        (first.hom.rationalFunction + second.hom.rationalFunction)
    congr 1
    change
      data.rationalFunctions.pullback first.hom.base
            second.hom.rationalFunction +
          second.hom.frobeniusDegree.val • first.hom.rationalFunction = _
    have firstBaseIdentity := first.baseIdentity
    have secondLinear := second.linear
    change first.hom.base = 𝟙 _ at firstBaseIdentity
    change second.hom.frobeniusDegree = 1 at secondLinear
    rw [firstBaseIdentity, secondLinear,
      data.rationalFunctions.pullback_id]
    change second.hom.rationalFunction +
      (1 : ℕ) • first.hom.rationalFunction = _
    rw [one_nsmul]
    abel

/-- The rational-function coordinate determines an element of `O^triangle`
at the zero-divisor object uniquely. -/
theorem zeroObjectRationalFunctionHom_injective (base : D) :
    Function.Injective
      (zeroObjectRationalFunctionHom
        (Phi := Phi) (data := data) base) := by
  intro first second equality
  have rationalFunction_eq :
      first.hom.rationalFunction = second.hom.rationalFunction := by
    exact congrArg (fun value => value.1.toAdd) equality
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · exact first.linear.trans second.linear.symm
  · exact first.baseIdentity.trans second.baseIdentity.symm
  · let M := Phi.obj (Object.base (zeroObject Phi data base))
    letI : IsLeftCancelAdd M.carrier :=
      ⟨fun a b c h => M.integral a b c h⟩
    letI : IsCancelAdd M.carrier :=
      AddCommMagma.IsLeftCancelAdd.toIsCancelAdd M.carrier
    apply Algebra.GrothendieckAddGroup.of_injective
    rw [zeroObject_endomorphism_balance
      (Phi := Phi) (data := data) base first]
    rw [zeroObject_endomorphism_balance
      (Phi := Phi) (data := data) base second]
    exact congrArg (data.divisor base) rationalFunction_eq
  · exact rationalFunction_eq

/-- Every effective rational function gives an element of `O^triangle` at the
zero-divisor object by using its uniquely determined effective divisor. -/
theorem zeroObjectRationalFunctionHom_surjective (base : D) :
    Function.Surjective
      (zeroObjectRationalFunctionHom
        (Phi := Phi) (data := data) base) := by
  intro value
  rcases value.2 with ⟨divisor, divisor_eq⟩
  let hom :
      Hom Phi data (zeroObject Phi data base) (zeroObject Phi data base) :=
    { frobeniusDegree := 1
      base := 𝟙 (Object.base (zeroObject Phi data base))
      divisor := divisor
      rationalFunction := value.1.toAdd
      balance := by
        have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
        simpa only [zeroObject_divisorClass_eq_zero, degreeOne, one_nsmul,
          map_zero, zero_add] using divisor_eq }
  let endomorphism :
      P.LinearBaseIdentityEndomorphism (zeroObject Phi data base) :=
    { hom := hom
      linear := rfl
      baseIdentity := rfl }
  refine ⟨endomorphism, ?_⟩
  apply Subtype.ext
  rfl

/-- Frobenioids I, Theorem 5.2 and IUT II, Definition 4.9(iii), at one
zero-divisor base object: `O^triangle` is the effective part of the input
rational-function group. -/
def zeroObjectRationalFunctionEquiv (base : D) :
    P.LinearBaseIdentityEndomorphism (zeroObject Phi data base) ≃*
      effectiveRationalFunctionSubmonoid
        (Phi := Phi) (data := data) (zeroObject Phi data base) :=
  MulEquiv.ofBijective
    (zeroObjectRationalFunctionHom (Phi := Phi) (data := data) base)
    ⟨zeroObjectRationalFunctionHom_injective
        (Phi := Phi) (data := data) base,
      zeroObjectRationalFunctionHom_surjective
        (Phi := Phi) (data := data) base⟩

end

end Iut.SourceModelFrobenioid.Carrier
