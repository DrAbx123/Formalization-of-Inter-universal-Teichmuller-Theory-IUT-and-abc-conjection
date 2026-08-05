/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidRationalMonoidTransport

open CategoryTheory

/-!
# The isotropic base category of a Frobenioid

This file constructs the category `D*` of Frobenioids I, Proposition 2.2(i).
Its objects are isotropic objects of the Frobenioid and its morphisms are the
morphisms between their images in the base category.  The projection
`D* -> D` is proved to be an equivalence from the Frobenioid axioms.

No rational-monoid action on arbitrary base morphisms is asserted here.  That
is the separate Proposition 2.2(ii) extension needed before evaluation at a
universal covering pro-object.
-/

namespace Iut.FrobenioidIsotropicBase

universe u

noncomputable section

variable (F : FrobenioidPresentation.{u})

/-- The category `D*` of Frobenioids I, Proposition 2.2(i). -/
structure DStar where
  object : F.carrier
  isotropic : F.preFrobenioid.IsIsotropic object

instance : Category.{u} (DStar F) where
  Hom source target :=
    F.preFrobenioid.base.obj source.object ⟶
      F.preFrobenioid.base.obj target.object
  id source := 𝟙 (F.preFrobenioid.base.obj source.object)
  comp first second := first ≫ second
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

/-- Forget the `D*` object to the corresponding isotropic linear object. -/
def DStar.toIsotropicLinearObject (object : DStar F) :
    F.preFrobenioid.IsotropicLinearObject where
  obj := object.object
  isotropic := object.isotropic

/-- Regard an isotropic linear object as an object of `D*`. -/
def DStar.ofIsotropicLinearObject
    (object : F.preFrobenioid.IsotropicLinearObject) : DStar F where
  object := object.obj
  isotropic := object.isotropic

@[simp]
theorem DStar.to_of_isotropicLinearObject
    (object : F.preFrobenioid.IsotropicLinearObject) :
    (DStar.ofIsotropicLinearObject F object).toIsotropicLinearObject F = object :=
  rfl

@[simp]
theorem DStar.of_to_isotropicLinearObject (object : DStar F) :
    DStar.ofIsotropicLinearObject F (object.toIsotropicLinearObject F) = object :=
  rfl

/-- The tautological projection `D* -> D`. -/
def projection : DStar F ⥤ F.baseCategory where
  obj object := F.preFrobenioid.base.obj object.object
  map arrow := arrow
  map_id _ := rfl
  map_comp _ _ := rfl

instance projection_faithful : (projection F).Faithful where
  map_injective equality := equality

instance projection_full : (projection F).Full where
  map_surjective arrow := ⟨arrow, rfl⟩

/-- Every base object has an isotropic representative: take an object supplied
by Definition 1.3(i)(a), then pass to an isotropic hull. -/
instance projection_essSurj : (projection F).EssSurj where
  mem_essImage baseObject := by
    let represented := Classical.choose
      (F.axioms.baseRepresented baseObject)
    have representedProperty := Classical.choose_spec
      (F.axioms.baseRepresented baseObject)
    let hull := Classical.choice
      (F.axioms.isotropicHull represented)
    have hullBaseIsIso :
        IsIso (F.preFrobenioid.base.map hull.hom) :=
      hull.preStep.2
    letI : IsIso (F.preFrobenioid.base.map hull.hom) :=
      hullBaseIsIso
    let representedBaseIso := Classical.choice representedProperty.2
    refine ⟨{ object := hull.hull, isotropic := hull.isotropic }, ?_⟩
    exact ⟨(asIso (F.preFrobenioid.base.map hull.hom)).symm ≪≫
      representedBaseIso⟩

instance projection_isEquivalence : (projection F).IsEquivalence where

/-- Frobenioids I, Proposition 2.2(i): `D*` is equivalent to the base
category `D`. -/
def equivalence : DStar F ≌ F.baseCategory :=
  (projection F).asEquivalence

end

end Iut.FrobenioidIsotropicBase
