/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidZeroEvaluation
import Iut.Foundations.SourceModelRationalMonoidTransport

/-!
# Naturality of integral evaluation in the model Frobenioid

The zero-divisor section of the model Frobenioid identifies `O^triangle`
naturally with the submonoid of rational functions whose divisor is effective.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid.Carrier

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : forall {X Y : D}, (X ⟶ Y) -> Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

private abbrev P := preFrobenioid (Phi := Phi) (data := data)

def zeroIsotropicLinearFunctor : D ⥤
    (preFrobenioid (Phi := Phi) (data := data)).IsotropicLinearObject where
  obj base :=
    { obj := zeroObject (Phi := Phi) (data := data) base
      isotropic := isIsotropic (Phi := Phi) (data := data)
        (zeroObject Phi data base) }
  map arrow :=
    { hom := zeroBaseArrow Phi data arrow
      linear := rfl }
  map_id object := by
    apply PreFrobenioid.IsotropicLinearHom.ext
    rfl
  map_comp first second := by
    apply PreFrobenioid.IsotropicLinearHom.ext
    apply Hom.ext
    · rfl
    · rfl
    · simp [zeroBaseArrow]
    · simp [zeroBaseArrow]

def zeroRationalMonoidFunctor : Dᵒᵖ ⥤ MonCat.{u} :=
  (zeroIsotropicLinearFunctor (Phi := Phi) (data := data)).op ⋙
    (rationalMonoidTransport (Phi := Phi) (data := data)).functor

def effectiveRationalFunctionPullback
    {source target : D} (arrow : source ⟶ target) :
    effectiveRationalFunctionSubmonoid
        (Phi := Phi) (data := data) (zeroObject Phi data target) →*
      effectiveRationalFunctionSubmonoid
        (Phi := Phi) (data := data) (zeroObject Phi data source) where
  toFun value :=
    ⟨Multiplicative.ofAdd
        (data.rationalFunctions.pullback arrow value.1.toAdd), by
      rcases value.2 with ⟨divisor, divisor_eq⟩
      change (Phi.obj target).carrier at divisor
      change Algebra.GrothendieckAddGroup.of divisor =
        data.divisor target value.1.toAdd at divisor_eq
      refine ⟨Phi.pullback arrow divisor, ?_⟩
      change
        Algebra.GrothendieckAddGroup.of (Phi.pullback arrow divisor) =
          data.divisor source
            (data.rationalFunctions.pullback arrow value.1.toAdd)
      rw [data.divisor_natural, ← divisor_eq, gpPullback_of]⟩
  map_one' := by
    apply Subtype.ext
    change Multiplicative.ofAdd
        (data.rationalFunctions.pullback arrow 0) = 1
    rw [map_zero]
    rfl
  map_mul' first second := by
    apply Subtype.ext
    exact congrArg Multiplicative.ofAdd
      (map_add (data.rationalFunctions.pullback arrow)
        first.1.toAdd second.1.toAdd)

def effectiveRationalFunctionFunctor : Dᵒᵖ ⥤ MonCat.{u} where
  obj base := MonCat.of
    (effectiveRationalFunctionSubmonoid
      (Phi := Phi) (data := data) (zeroObject Phi data base.unop))
  map arrow := MonCat.ofHom
    (effectiveRationalFunctionPullback
      (Phi := Phi) (data := data) arrow.unop)
  map_id base := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro value
    apply Subtype.ext
    change Multiplicative.ofAdd
        (data.rationalFunctions.pullback (𝟙 base.unop) value.1.toAdd) =
      value.1
    rw [data.rationalFunctions.pullback_id]
    rfl
  map_comp first second := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro value
    apply Subtype.ext
    change Multiplicative.ofAdd
        (data.rationalFunctions.pullback (second.unop ≫ first.unop)
          value.1.toAdd) =
      Multiplicative.ofAdd
        (data.rationalFunctions.pullback second.unop
          (data.rationalFunctions.pullback first.unop value.1.toAdd))
    rw [data.rationalFunctions.pullback_comp]
    rfl

def zeroRationalFunctionIsoApp (base : Dᵒᵖ) :
    (zeroRationalMonoidFunctor (Phi := Phi) (data := data)).obj base ≅
      (effectiveRationalFunctionFunctor
        (Phi := Phi) (data := data)).obj base where
  hom := MonCat.ofHom
    (zeroObjectRationalFunctionEquiv
      (Phi := Phi) (data := data) base.unop).toMonoidHom
  inv := MonCat.ofHom
    (zeroObjectRationalFunctionEquiv
      (Phi := Phi) (data := data) base.unop).symm.toMonoidHom
  hom_inv_id := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro value
    exact (zeroObjectRationalFunctionEquiv
      (Phi := Phi) (data := data) base.unop).symm_apply_apply value
  inv_hom_id := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro value
    exact (zeroObjectRationalFunctionEquiv
      (Phi := Phi) (data := data) base.unop).apply_symm_apply value

def zeroRationalFunctionNatIso :
    zeroRationalMonoidFunctor (Phi := Phi) (data := data) ≅
      effectiveRationalFunctionFunctor (Phi := Phi) (data := data) :=
  NatIso.ofComponents
    (zeroRationalFunctionIsoApp (Phi := Phi) (data := data))
    (fun {source target} arrow => by
      apply MonCat.hom_ext
      apply MonoidHom.ext
      intro value
      change P.LinearBaseIdentityEndomorphism
        (zeroObject Phi data source.unop) at value
      apply Subtype.ext
      change Multiplicative.ofAdd
          (data.rationalFunctions.pullback arrow.unop
            value.hom.rationalFunction) =
        Multiplicative.ofAdd
          (data.rationalFunctions.pullback arrow.unop
            value.hom.rationalFunction)
      rfl)

end

end Iut.SourceModelFrobenioid.Carrier
