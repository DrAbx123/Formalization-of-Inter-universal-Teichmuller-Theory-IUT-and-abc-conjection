/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Images in a Galois category

This file constructs the canonical range action of a morphism of finite
group-actions and lifts it through a fiber functor.  It yields epi-mono image
factorizations in an arbitrary Galois category and the canonical comparison
of two such factorizations under an isomorphism square.
-/

namespace CategoryTheory

universe u v

open Limits
open PreGaloisCategory

namespace Action

variable (G : Type v) [Group G]

noncomputable def range {X Y : Action FintypeCat.{u} G}
    (f : X ⟶ Y) : Action FintypeCat.{u} G where
  V := FintypeCat.of (Set.range f.hom)
  ρ := {
    toFun g := FintypeCat.homMk (fun y =>
      ⟨(Y.ρ g).hom y.1, by
        rcases y.2 with ⟨x, hx⟩
        refine ⟨(X.ρ g).hom x, ?_⟩
        calc
          f.hom ((X.ρ g).hom x) = (Y.ρ g).hom (f.hom x) := by
            simpa only [← FintypeCat.comp_apply] using
              ConcreteCategory.congr_hom (f.comm g) x
          _ = (Y.ρ g).hom y.1 := congrArg _ hx⟩)
    map_one' := by aesop
    map_mul' := by aesop }

noncomputable def rangeIncl {X Y : Action FintypeCat.{u} G}
    (f : X ⟶ Y) : Action.range G f ⟶ Y where
  hom := FintypeCat.homMk Subtype.val
  comm _ := by
    ext y
    rfl

noncomputable def toRange {X Y : Action FintypeCat.{u} G}
    (f : X ⟶ Y) : X ⟶ Action.range G f where
  hom := FintypeCat.homMk (fun x => ⟨f.hom x, ⟨x, rfl⟩⟩)
  comm g := by
    ext x
    apply Subtype.ext
    simpa only [FintypeCat.comp_apply] using
      ConcreteCategory.congr_hom (f.comm g) x

theorem toRange_comp_rangeIncl {X Y : Action FintypeCat.{u} G}
    (f : X ⟶ Y) : toRange G f ≫ rangeIncl G f = f := by
  ext x
  simp only [Action.comp_hom, FintypeCat.comp_apply]
  rfl

instance {X Y : Action FintypeCat.{u} G} (f : X ⟶ Y) :
    Mono (rangeIncl G f) := by
  apply ConcreteCategory.mono_of_injective
  change Function.Injective Subtype.val
  exact Subtype.val_injective

instance {X Y : Action FintypeCat.{u} G} (f : X ⟶ Y) :
    Epi (toRange G f) := by
  apply ConcreteCategory.epi_of_surjective
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

end Action

namespace PreGaloisCategory

variable {C : Type (u + 1)} [Category.{u} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{u}) [FiberFunctor F]

noncomputable instance fiberFunctorReflectsEpimorphisms :
    F.ReflectsEpimorphisms where
  reflects f _ := by
    let H := functorToAction F
    have underlyingSurjective : Function.Surjective (F.map f) :=
      surjective_of_epi (FintypeCat.incl.map (F.map f))
    haveI : Epi (H.map f) :=
      ConcreteCategory.epi_of_surjective _ underlyingSurjective
    exact H.epi_of_epi_map inferInstance

structure ImageFactorization {X Y : C} (f : X ⟶ Y) where
  image : C
  projection : X ⟶ image
  inclusion : image ⟶ Y
  projection_epi : Epi projection
  inclusion_mono : Mono inclusion
  fac : projection ≫ inclusion = f

attribute [instance] ImageFactorization.projection_epi
  ImageFactorization.inclusion_mono

noncomputable def imageFactorization {X Y : C} (f : X ⟶ Y) :
    ImageFactorization f := by
  let H := functorToAction F
  let R := Action.range (Aut F) (H.map f)
  let r : R ⟶ H.obj Y := Action.rangeIncl (Aut F) (H.map f)
  let witness := exists_lift_of_mono F Y R r
  let I := Classical.choose witness
  let m := Classical.choose (Classical.choose_spec witness)
  let e := Classical.choose
    (Classical.choose_spec (Classical.choose_spec witness))
  have properties := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec witness))
  have monoM : Mono m := properties.1
  have eComp : e.hom ≫ H.map m = r := properties.2
  let q : H.obj X ⟶ R := Action.toRange (Aut F) (H.map f)
  let p : X ⟶ I := H.preimage (q ≫ e.hom)
  have pEpi : Epi p := by
    apply H.epi_of_epi_map
    rw [H.map_preimage]
    infer_instance
  exact
    { image := I
      projection := p
      inclusion := m
      projection_epi := pEpi
      inclusion_mono := monoM
      fac := by
        apply H.map_injective
        rw [H.map_comp, H.map_preimage]
        rw [Category.assoc, eComp]
        exact Action.toRange_comp_rangeIncl (Aut F) (H.map f) }

noncomputable def imageComparisonPreimage
    {X₁ I₁ : C} (e₁ : X₁ ⟶ I₁) [Epi e₁]
    (point : F.obj I₁) : F.obj X₁ :=
  Classical.choose (surjective_on_fiber_of_epi F e₁ point)

theorem imageComparisonPreimage_spec
    {X₁ I₁ : C} (e₁ : X₁ ⟶ I₁) [Epi e₁]
    (point : F.obj I₁) :
    F.map e₁ (imageComparisonPreimage F e₁ point) = point :=
  Classical.choose_spec (surjective_on_fiber_of_epi F e₁ point)

noncomputable def imageComparisonLift
    {X₁ I₁ X₂ I₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (e₂ : X₂ ⟶ I₂)
    (x : X₁ ≅ X₂) (point : F.obj I₁) : F.obj I₂ :=
  F.map e₂ (F.map x.hom (imageComparisonPreimage F e₁ point))

theorem imageComparisonLift_inclusion
    {X₁ I₁ Y₁ X₂ I₂ Y₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (m₁ : I₁ ⟶ Y₁)
    (e₂ : X₂ ⟶ I₂) (m₂ : I₂ ⟶ Y₂)
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : e₁ ≫ m₁ ≫ y.hom = x.hom ≫ e₂ ≫ m₂)
    (point : F.obj I₁) :
    F.map m₂ (imageComparisonLift F e₁ e₂ x point) =
      F.map y.hom (F.map m₁ point) := by
  have mappedSquare :
      F.map e₁ ≫ F.map m₁ ≫ F.map y.hom =
        F.map x.hom ≫ F.map e₂ ≫ F.map m₂ := by
    simpa only [← F.map_comp, Category.assoc] using congrArg F.map square
  have evaluated := ConcreteCategory.congr_hom mappedSquare
    (imageComparisonPreimage F e₁ point)
  simpa only [FintypeCat.comp_apply, imageComparisonLift,
    imageComparisonPreimage_spec] using evaluated.symm

noncomputable def imageComparisonActionHom
    {X₁ I₁ Y₁ X₂ I₂ Y₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (m₁ : I₁ ⟶ Y₁)
    (e₂ : X₂ ⟶ I₂) (m₂ : I₂ ⟶ Y₂) [Mono m₂]
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : e₁ ≫ m₁ ≫ y.hom = x.hom ≫ e₂ ≫ m₂) :
    (functorToAction F).obj I₁ ⟶ (functorToAction F).obj I₂ := by
  let lift := imageComparisonLift F e₁ e₂ x
  have inclusion_spec (point : F.obj I₁) :
      F.map m₂ (lift point) = F.map y.hom (F.map m₁ point) :=
    imageComparisonLift_inclusion F e₁ m₁ e₂ m₂ x y square point
  have inclusionInjective : Function.Injective (F.map m₂) := by
    apply (mono_iff_injective (FintypeCat.incl.map (F.map m₂))).mp
    infer_instance
  refine
    { hom := FintypeCat.homMk lift
      comm := fun g => ?_ }
  ext point
  apply inclusionInjective
  change F.map m₂ (lift (g.hom.app I₁ point)) =
    F.map m₂ (g.hom.app I₂ (lift point))
  calc
    F.map m₂ (lift (g.hom.app I₁ point)) =
        F.map y.hom (F.map m₁ (g.hom.app I₁ point)) := inclusion_spec _
    _ = F.map y.hom (g.hom.app Y₁ (F.map m₁ point)) := by
      exact congrArg (fun p => F.map y.hom p)
        (ConcreteCategory.congr_hom (g.hom.naturality m₁) point).symm
    _ = g.hom.app Y₂ (F.map y.hom (F.map m₁ point)) := by
      exact (ConcreteCategory.congr_hom
        (g.hom.naturality y.hom) (F.map m₁ point)).symm
    _ = g.hom.app Y₂ (F.map m₂ (lift point)) :=
      congrArg (fun p => g.hom.app Y₂ p) (inclusion_spec point).symm
    _ = F.map m₂ (g.hom.app I₂ (lift point)) :=
      ConcreteCategory.congr_hom (g.hom.naturality m₂) (lift point)

theorem imageComparisonActionHom_inclusion
    {X₁ I₁ Y₁ X₂ I₂ Y₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (m₁ : I₁ ⟶ Y₁)
    (e₂ : X₂ ⟶ I₂) (m₂ : I₂ ⟶ Y₂) [Mono m₂]
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : e₁ ≫ m₁ ≫ y.hom = x.hom ≫ e₂ ≫ m₂) :
    imageComparisonActionHom F e₁ m₁ e₂ m₂ x y square ≫
        (functorToAction F).map m₂ =
      (functorToAction F).map m₁ ≫ (functorToAction F).map y.hom := by
  ext point
  exact imageComparisonLift_inclusion F e₁ m₁ e₂ m₂ x y square point

theorem imageComparisonActionHom_projection
    {X₁ I₁ Y₁ X₂ I₂ Y₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (m₁ : I₁ ⟶ Y₁)
    (e₂ : X₂ ⟶ I₂) (m₂ : I₂ ⟶ Y₂) [Mono m₂]
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : e₁ ≫ m₁ ≫ y.hom = x.hom ≫ e₂ ≫ m₂) :
    (functorToAction F).map e₁ ≫
        imageComparisonActionHom F e₁ m₁ e₂ m₂ x y square =
      (functorToAction F).map x.hom ≫ (functorToAction F).map e₂ := by
  let H := functorToAction F
  apply (cancel_mono (H.map m₂)).1
  rw [Category.assoc, imageComparisonActionHom_inclusion]
  simpa only [H.map_comp, Category.assoc] using congrArg H.map square

noncomputable def imageComparison
    {X₁ I₁ Y₁ X₂ I₂ Y₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (m₁ : I₁ ⟶ Y₁)
    (e₂ : X₂ ⟶ I₂) (m₂ : I₂ ⟶ Y₂) [Mono m₂]
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : e₁ ≫ m₁ ≫ y.hom = x.hom ≫ e₂ ≫ m₂) : I₁ ⟶ I₂ :=
  (functorToAction F).preimage
    (imageComparisonActionHom F e₁ m₁ e₂ m₂ x y square)

theorem imageComparison_inclusion
    {X₁ I₁ Y₁ X₂ I₂ Y₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (m₁ : I₁ ⟶ Y₁)
    (e₂ : X₂ ⟶ I₂) (m₂ : I₂ ⟶ Y₂) [Mono m₂]
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : e₁ ≫ m₁ ≫ y.hom = x.hom ≫ e₂ ≫ m₂) :
    imageComparison F e₁ m₁ e₂ m₂ x y square ≫ m₂ = m₁ ≫ y.hom := by
  apply (functorToAction F).map_injective
  simpa only [imageComparison, Functor.map_comp, Functor.map_preimage] using
    imageComparisonActionHom_inclusion F e₁ m₁ e₂ m₂ x y square

theorem imageComparison_projection
    {X₁ I₁ Y₁ X₂ I₂ Y₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (m₁ : I₁ ⟶ Y₁)
    (e₂ : X₂ ⟶ I₂) (m₂ : I₂ ⟶ Y₂) [Mono m₂]
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : e₁ ≫ m₁ ≫ y.hom = x.hom ≫ e₂ ≫ m₂) :
    e₁ ≫ imageComparison F e₁ m₁ e₂ m₂ x y square = x.hom ≫ e₂ := by
  apply (functorToAction F).map_injective
  simpa only [imageComparison, Functor.map_comp, Functor.map_preimage] using
    imageComparisonActionHom_projection F e₁ m₁ e₂ m₂ x y square

noncomputable def imageComparisonIso
    {X₁ I₁ Y₁ X₂ I₂ Y₂ : C}
    (e₁ : X₁ ⟶ I₁) [Epi e₁] (m₁ : I₁ ⟶ Y₁) [Mono m₁]
    (e₂ : X₂ ⟶ I₂) [Epi e₂] (m₂ : I₂ ⟶ Y₂) [Mono m₂]
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : e₁ ≫ m₁ ≫ y.hom = x.hom ≫ e₂ ≫ m₂) : I₁ ≅ I₂ := by
  let reverseSquare :
      e₂ ≫ m₂ ≫ y.inv = x.inv ≫ e₁ ≫ m₁ := by
    rw [← cancel_epi x.hom]
    rw [← cancel_mono y.hom]
    simpa [Category.assoc] using square.symm
  let forward := imageComparison F e₁ m₁ e₂ m₂ x y square
  let reverse := imageComparison F e₂ m₂ e₁ m₁ x.symm y.symm reverseSquare
  exact
    { hom := forward
      inv := reverse
      hom_inv_id := by
        apply (cancel_epi e₁).1
        change e₁ ≫ (forward ≫ reverse) = e₁ ≫ 𝟙 I₁
        rw [← Category.assoc]
        rw [imageComparison_projection F e₁ m₁ e₂ m₂ x y square]
        rw [Category.assoc]
        rw [imageComparison_projection F e₂ m₂ e₁ m₁ x.symm y.symm reverseSquare]
        simp
      inv_hom_id := by
        apply (cancel_epi e₂).1
        change e₂ ≫ (reverse ≫ forward) = e₂ ≫ 𝟙 I₂
        rw [← Category.assoc]
        rw [imageComparison_projection F e₂ m₂ e₁ m₁ x.symm y.symm reverseSquare]
        rw [Category.assoc]
        rw [imageComparison_projection F e₁ m₁ e₂ m₂ x y square]
        simp }

end PreGaloisCategory

end CategoryTheory
