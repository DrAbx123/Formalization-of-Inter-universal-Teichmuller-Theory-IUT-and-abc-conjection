/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Canonical comparison of direct-summand complements

In a Galois category, the complement of a fixed coproduct injection is
canonical.  This file makes the resulting comparison explicit and functorial
under isomorphism squares.  The proof uses the existing full functor to finite
actions: on fibers, both complements are exactly the set-theoretic complement
of the image of the mono.
-/

namespace CategoryTheory.PreGaloisCategory

universe u

open CategoryTheory Limits

variable {C : Type (u + 1)} [Category.{u} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{u}) [FiberFunctor F]

theorem complementTarget_mem
    {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (u₁ : Z₁ ⟶ Y₁)
    (i₂ : X₂ ⟶ Y₂) (u₂ : Z₂ ⟶ Y₂)
    (h₁ : IsColimit (BinaryCofan.mk i₁ u₁))
    (h₂ : IsColimit (BinaryCofan.mk i₂ u₂))
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : i₁ ≫ y.hom = x.hom ≫ i₂)
    (z : F.obj Z₁) :
    F.map y.hom (F.map u₁ z) ∈ Set.range (F.map u₂) := by
  let mapped₁ := mapIsColimitOfPreservesOfIsColimit F i₁ u₁ h₁
  let mapped₂ := mapIsColimitOfPreservesOfIsColimit F i₂ u₂ h₂
  let mapped₁Types := mapIsColimitOfPreservesOfIsColimit
    FintypeCat.incl (F.map i₁) (F.map u₁) mapped₁
  let mapped₂Types := mapIsColimitOfPreservesOfIsColimit
    FintypeCat.incl (F.map i₂) (F.map u₂) mapped₂
  have facts₁ := (Types.binaryCofan_isColimit_iff
    (BinaryCofan.mk (FintypeCat.incl.map (F.map i₁))
      (FintypeCat.incl.map (F.map u₁)))).mp ⟨mapped₁Types⟩
  have facts₂ := (Types.binaryCofan_isColimit_iff
    (BinaryCofan.mk (FintypeCat.incl.map (F.map i₂))
      (FintypeCat.incl.map (F.map u₂)))).mp ⟨mapped₂Types⟩
  have facts₁' : Function.Injective (F.map i₁) ∧
      Function.Injective (F.map u₁) ∧
      IsCompl (Set.range (F.map i₁)) (Set.range (F.map u₁)) := by
    simpa using facts₁
  have facts₂' : Function.Injective (F.map i₂) ∧
      Function.Injective (F.map u₂) ∧
      IsCompl (Set.range (F.map i₂)) (Set.range (F.map u₂)) := by
    simpa using facts₂
  rw [← facts₂'.2.2.compl_eq]
  rw [Set.mem_compl_iff]
  rintro ⟨a, ha⟩
  have mappedSquare :
      F.map i₁ ≫ F.map y.hom = F.map x.hom ≫ F.map i₂ := by
    simpa only [← F.map_comp] using congrArg F.map square
  have evaluatedSquare := ConcreteCategory.congr_hom mappedSquare (F.map x.inv a)
  have inverseCancellation : F.map x.hom (F.map x.inv a) = a := by
    calc
      F.map x.hom (F.map x.inv a) = F.map (x.inv ≫ x.hom) a := by
        rw [F.map_comp, FintypeCat.comp_apply]
      _ = F.map (𝟙 X₂) a := by rw [x.inv_hom_id]
      _ = a := by simp
  have leftMapsToTarget :
      F.map y.hom (F.map i₁ (F.map x.inv a)) =
        F.map y.hom (F.map u₁ z) := by
    rw [← ha]
    simpa only [FintypeCat.comp_apply, inverseCancellation] using evaluatedSquare
  have yCancellation (point : F.obj Y₁) :
      F.map y.inv (F.map y.hom point) = point := by
    calc
      F.map y.inv (F.map y.hom point) =
          F.map (y.hom ≫ y.inv) point := by
        rw [F.map_comp, FintypeCat.comp_apply]
      _ = F.map (𝟙 Y₁) point := by rw [y.hom_inv_id]
      _ = point := by simp
  have leftEquals : F.map i₁ (F.map x.inv a) = F.map u₁ z := by
    calc
      F.map i₁ (F.map x.inv a) =
          F.map y.inv (F.map y.hom (F.map i₁ (F.map x.inv a))) :=
        (yCancellation _).symm
      _ = F.map y.inv (F.map y.hom (F.map u₁ z)) := congrArg _ leftMapsToTarget
      _ = F.map u₁ z := yCancellation _
  have both : F.map u₁ z ∈
      Set.range (F.map i₁) ⊓ Set.range (F.map u₁) := by
    exact ⟨⟨F.map x.inv a, leftEquals⟩, ⟨z, rfl⟩⟩
  rw [disjoint_iff.mp facts₁'.2.2.1] at both
  exact both.elim

noncomputable def complementComparisonActionHom
    {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (u₁ : Z₁ ⟶ Y₁)
    (i₂ : X₂ ⟶ Y₂) (u₂ : Z₂ ⟶ Y₂)
    (h₁ : IsColimit (BinaryCofan.mk i₁ u₁))
    (h₂ : IsColimit (BinaryCofan.mk i₂ u₂))
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : i₁ ≫ y.hom = x.hom ≫ i₂) :
    (functorToAction F).obj Z₁ ⟶ (functorToAction F).obj Z₂ := by
  let mapped₁ := mapIsColimitOfPreservesOfIsColimit F i₁ u₁ h₁
  let mapped₂ := mapIsColimitOfPreservesOfIsColimit F i₂ u₂ h₂
  let mapped₁Types := mapIsColimitOfPreservesOfIsColimit
    FintypeCat.incl (F.map i₁) (F.map u₁) mapped₁
  let mapped₂Types := mapIsColimitOfPreservesOfIsColimit
    FintypeCat.incl (F.map i₂) (F.map u₂) mapped₂
  have facts₁ := (Types.binaryCofan_isColimit_iff
    (BinaryCofan.mk (FintypeCat.incl.map (F.map i₁))
      (FintypeCat.incl.map (F.map u₁)))).mp ⟨mapped₁Types⟩
  have facts₂ := (Types.binaryCofan_isColimit_iff
    (BinaryCofan.mk (FintypeCat.incl.map (F.map i₂))
      (FintypeCat.incl.map (F.map u₂)))).mp ⟨mapped₂Types⟩
  have facts₁' : Function.Injective (F.map i₁) ∧
      Function.Injective (F.map u₁) ∧
      IsCompl (Set.range (F.map i₁)) (Set.range (F.map u₁)) := by
    simpa using facts₁
  have facts₂' : Function.Injective (F.map i₂) ∧
      Function.Injective (F.map u₂) ∧
      IsCompl (Set.range (F.map i₂)) (Set.range (F.map u₂)) := by
    simpa using facts₂
  let target (z : F.obj Z₁) : F.obj Y₂ := F.map y.hom (F.map u₁ z)
  have target_mem (z : F.obj Z₁) :
      target z ∈ Set.range (F.map u₂) :=
    complementTarget_mem F i₁ u₁ i₂ u₂ h₁ h₂ x y square z
  let lift (z : F.obj Z₁) : F.obj Z₂ := Classical.choose (target_mem z)
  have lift_spec (z : F.obj Z₁) : F.map u₂ (lift z) = target z :=
    Classical.choose_spec (target_mem z)
  refine
    { hom := FintypeCat.homMk lift
      comm := fun g => ?_ }
  ext z
  apply facts₂'.2.1
  change F.map u₂ (lift (g.hom.app Z₁ z)) =
    F.map u₂ (g.hom.app Z₂ (lift z))
  calc
    F.map u₂ (lift (g.hom.app Z₁ z)) =
        target (g.hom.app Z₁ z) := lift_spec _
    _ = F.map y.hom (F.map u₁ (g.hom.app Z₁ z)) := rfl
    _ = F.map y.hom (g.hom.app Y₁ (F.map u₁ z)) := by
      exact congrArg (fun point => F.map y.hom point)
        (ConcreteCategory.congr_hom (g.hom.naturality u₁) z).symm
    _ = g.hom.app Y₂ (F.map y.hom (F.map u₁ z)) := by
      exact (ConcreteCategory.congr_hom
        (g.hom.naturality y.hom) (F.map u₁ z)).symm
    _ = g.hom.app Y₂ (target z) := rfl
    _ = g.hom.app Y₂ (F.map u₂ (lift z)) :=
      congrArg (fun point => g.hom.app Y₂ point) (lift_spec z).symm
    _ = F.map u₂ (g.hom.app Z₂ (lift z)) :=
      ConcreteCategory.congr_hom (g.hom.naturality u₂) (lift z)

theorem complementComparisonActionHom_comp
    {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (u₁ : Z₁ ⟶ Y₁)
    (i₂ : X₂ ⟶ Y₂) (u₂ : Z₂ ⟶ Y₂)
    (h₁ : IsColimit (BinaryCofan.mk i₁ u₁))
    (h₂ : IsColimit (BinaryCofan.mk i₂ u₂))
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : i₁ ≫ y.hom = x.hom ≫ i₂) :
    complementComparisonActionHom F i₁ u₁ i₂ u₂ h₁ h₂ x y square ≫
        (functorToAction F).map u₂ =
      (functorToAction F).map u₁ ≫ (functorToAction F).map y.hom := by
  ext z
  simp only [Action.comp_hom, functorToAction_map, FintypeCat.comp_apply]
  exact Classical.choose_spec
    (complementTarget_mem F i₁ u₁ i₂ u₂ h₁ h₂ x y square z)

noncomputable def complementComparison
    {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (u₁ : Z₁ ⟶ Y₁)
    (i₂ : X₂ ⟶ Y₂) (u₂ : Z₂ ⟶ Y₂)
    (h₁ : IsColimit (BinaryCofan.mk i₁ u₁))
    (h₂ : IsColimit (BinaryCofan.mk i₂ u₂))
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : i₁ ≫ y.hom = x.hom ≫ i₂) : Z₁ ⟶ Z₂ :=
  (functorToAction F).preimage
    (complementComparisonActionHom F i₁ u₁ i₂ u₂ h₁ h₂ x y square)

theorem complementComparison_comp
    {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (u₁ : Z₁ ⟶ Y₁)
    (i₂ : X₂ ⟶ Y₂) (u₂ : Z₂ ⟶ Y₂)
    (h₁ : IsColimit (BinaryCofan.mk i₁ u₁))
    (h₂ : IsColimit (BinaryCofan.mk i₂ u₂))
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : i₁ ≫ y.hom = x.hom ≫ i₂) :
    complementComparison F i₁ u₁ i₂ u₂ h₁ h₂ x y square ≫ u₂ =
      u₁ ≫ y.hom := by
  apply (functorToAction F).map_injective
  simpa only [complementComparison, Functor.map_comp,
    Functor.map_preimage] using
    complementComparisonActionHom_comp F i₁ u₁ i₂ u₂ h₁ h₂ x y square

include F in
theorem mono_right_of_isColimit_binaryCofan
    {X Z Y : C} (i : X ⟶ Y) (u : Z ⟶ Y)
    (h : IsColimit (BinaryCofan.mk i u)) : Mono u := by
  let mapped := mapIsColimitOfPreservesOfIsColimit F i u h
  let mappedTypes := mapIsColimitOfPreservesOfIsColimit
    FintypeCat.incl (F.map i) (F.map u) mapped
  have facts := (Types.binaryCofan_isColimit_iff
    (BinaryCofan.mk (FintypeCat.incl.map (F.map i))
      (FintypeCat.incl.map (F.map u)))).mp ⟨mappedTypes⟩
  apply (functorToAction F).mono_of_mono_map
  apply (forget₂ (Action FintypeCat (Aut F)) FintypeCat).mono_of_mono_map
  apply FintypeCat.incl.mono_of_mono_map
  rw [mono_iff_injective]
  simpa using facts.2.1

theorem complementComparison_unique
    {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (u₁ : Z₁ ⟶ Y₁)
    (i₂ : X₂ ⟶ Y₂) (u₂ : Z₂ ⟶ Y₂)
    (h₁ : IsColimit (BinaryCofan.mk i₁ u₁))
    (h₂ : IsColimit (BinaryCofan.mk i₂ u₂))
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : i₁ ≫ y.hom = x.hom ≫ i₂)
    (candidate : Z₁ ⟶ Z₂)
    (candidate_comp : candidate ≫ u₂ = u₁ ≫ y.hom) :
    candidate = complementComparison F i₁ u₁ i₂ u₂ h₁ h₂ x y square := by
  letI : Mono u₂ := mono_right_of_isColimit_binaryCofan F i₂ u₂ h₂
  apply (cancel_mono u₂).1
  rw [candidate_comp, complementComparison_comp]

noncomputable def complementComparisonIso
    {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (u₁ : Z₁ ⟶ Y₁)
    (i₂ : X₂ ⟶ Y₂) (u₂ : Z₂ ⟶ Y₂)
    (h₁ : IsColimit (BinaryCofan.mk i₁ u₁))
    (h₂ : IsColimit (BinaryCofan.mk i₂ u₂))
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂)
    (square : i₁ ≫ y.hom = x.hom ≫ i₂) : Z₁ ≅ Z₂ where
  hom := complementComparison F i₁ u₁ i₂ u₂ h₁ h₂ x y square
  inv := complementComparison F i₂ u₂ i₁ u₁ h₂ h₁ x.symm y.symm (by
    rw [← cancel_mono y.hom]
    simp [Category.assoc, square])
  hom_inv_id := by
    letI : Mono u₁ := mono_right_of_isColimit_binaryCofan F i₁ u₁ h₁
    apply (cancel_mono u₁).1
    rw [Category.assoc, complementComparison_comp]
    rw [← Category.assoc, complementComparison_comp]
    simp
  inv_hom_id := by
    letI : Mono u₂ := mono_right_of_isColimit_binaryCofan F i₂ u₂ h₂
    apply (cancel_mono u₂).1
    rw [Category.assoc, complementComparison_comp]
    rw [← Category.assoc, complementComparison_comp]
    simp

end CategoryTheory.PreGaloisCategory
