/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperoidComponentFamily

/-!
# Restricting countable families of finite-action components

Restriction from a profinite group to a source group may split one orbit into
several smaller orbits. This file records the canonical decomposition of a
countable family of selected finite orbits after restriction.
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

/-- The finite action obtained by restricting along a continuous group
homomorphism. -/
noncomputable abbrev sourceFiniteRestrictionAction
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target) :
    ContAction FintypeCat.{u} source :=
  (ContAction.res FintypeCat homomorphism.hom).obj action

/-- Forget a restricted-group orbit down to the containing target-group
orbit. -/
noncomputable def sourceFiniteRestrictionComponentMap
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target) :
    SourceActionComponent source
        (sourceFiniteRestrictionAction homomorphism action) →
      SourceActionComponent target action :=
  Quotient.map' id (by
    intro first second relation
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
    obtain ⟨element, equality⟩ := relation
    exact ⟨homomorphism element, equality⟩)

@[simp]
theorem sourceFiniteRestrictionComponentMap_mk
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (point : action.obj.V) :
    sourceFiniteRestrictionComponentMap homomorphism action
        (Quotient.mk'' point) = Quotient.mk'' point :=
  rfl

/-- The components occurring after restricting a family of selected target
orbits. -/
abbrev SourceRestrictedComponentFamilyIndex
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u)
    (component : Index → SourceActionComponent target action) :=
  Σ index : Index,
    {restrictedComponent : SourceActionComponent source
        (sourceFiniteRestrictionAction homomorphism action) //
      sourceFiniteRestrictionComponentMap homomorphism action
          restrictedComponent = component index}

noncomputable instance sourceRestrictedComponentFamilyIndex_countable
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent target action) :
    Countable (SourceRestrictedComponentFamilyIndex
      homomorphism action Index component) :=
  inferInstance

/-- Restriction does not change any points; it only refines the orbit index. -/
noncomputable def sourceRestrictedComponentFamilyCarrierEquiv
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u)
    (component : Index → SourceActionComponent target action) :
    SourceTemperoidComponentFamilyCarrier target action Index component ≃
      SourceTemperoidComponentFamilyCarrier source
        (sourceFiniteRestrictionAction homomorphism action)
        (SourceRestrictedComponentFamilyIndex
          homomorphism action Index component)
        (fun index ↦ index.2.1) where
  toFun point :=
    ⟨⟨point.1,
        ⟨Quotient.mk'' point.2.1, by
          exact (sourceFiniteRestrictionComponentMap_mk
            homomorphism action point.2.1).trans point.2.2⟩⟩,
      ⟨point.2.1, rfl⟩⟩
  invFun point :=
    ⟨point.1.1,
      ⟨point.2.1, by
        calc
          Quotient.mk'' point.2.1 =
              sourceFiniteRestrictionComponentMap homomorphism action
                (Quotient.mk'' point.2.1) :=
            (sourceFiniteRestrictionComponentMap_mk
              homomorphism action point.2.1).symm
          _ = sourceFiniteRestrictionComponentMap homomorphism action
                point.1.2.1 := congrArg
            (sourceFiniteRestrictionComponentMap homomorphism action)
            point.2.2
          _ = component point.1.1 := point.1.2.2⟩⟩
  left_inv point := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      rfl
  right_inv point := by
    rcases point with ⟨⟨index, restrictedComponent, compatibility⟩,
      point, pointComponent⟩
    change Quotient.mk'' point = restrictedComponent at pointComponent
    subst restrictedComponent
    rfl

@[simp]
theorem sourceRestrictedComponentFamilyCarrierEquiv_apply_index
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u)
    (component : Index → SourceActionComponent target action)
    (point : SourceTemperoidComponentFamilyCarrier
      target action Index component) :
    (sourceRestrictedComponentFamilyCarrierEquiv
      homomorphism action Index component point).1.1 = point.1 :=
  rfl

@[simp]
theorem sourceRestrictedComponentFamilyCarrierEquiv_apply_val
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u)
    (component : Index → SourceActionComponent target action)
    (point : SourceTemperoidComponentFamilyCarrier
      target action Index component) :
    (sourceRestrictedComponentFamilyCarrierEquiv
      homomorphism action Index component point).2.1 = point.2.1 :=
  rfl

@[simp]
theorem sourceRestrictedComponentFamilyCarrierEquiv_symm_apply_val
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u)
    (component : Index → SourceActionComponent target action)
    (point : SourceTemperoidComponentFamilyCarrier source
      (sourceFiniteRestrictionAction homomorphism action)
      (SourceRestrictedComponentFamilyIndex
        homomorphism action Index component)
      (fun index => index.2.1)) :
    ((sourceRestrictedComponentFamilyCarrierEquiv
      homomorphism action Index component).symm point).2.1 = point.2.1 :=
  rfl

/-- Restricting a repeated family of target-group components is isomorphic to
the repeated family of all source-group components lying above them. -/
noncomputable def sourceRestrictedComponentFamilyActionIso
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent target action) :
    (ContAction.res SourceCountableTypeCat homomorphism.hom).obj
        (sourceTemperoidComponentFamilyAction
          target action Index component) ≅
      sourceTemperoidComponentFamilyAction source
        (sourceFiniteRestrictionAction homomorphism action)
        (SourceRestrictedComponentFamilyIndex
          homomorphism action Index component)
        (fun index ↦ index.2.1) := by
  let carrierEquiv := sourceRestrictedComponentFamilyCarrierEquiv
    homomorphism action Index component
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk carrierEquiv
        inv := SourceCountableTypeCat.homMk carrierEquiv.symm
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro point
          exact carrierEquiv.symm_apply_apply point
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro point
          exact carrierEquiv.apply_symm_apply point }
  · intro element
    apply ConcreteCategory.hom_ext
    intro point
    apply carrierEquiv.symm.injective
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      rfl

@[simp]
theorem sourceRestrictedComponentFamilyActionIso_hom_apply_val
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent target action)
    (point : SourceTemperoidComponentFamilyCarrier
      target action Index component) :
    ((sourceRestrictedComponentFamilyActionIso homomorphism action Index
      component).hom.hom.hom point).2.1 = point.2.1 :=
  rfl

@[simp]
theorem sourceRestrictedComponentFamilyActionIso_inv_apply_val
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent target action)
    (point : SourceTemperoidComponentFamilyCarrier source
      (sourceFiniteRestrictionAction homomorphism action)
      (SourceRestrictedComponentFamilyIndex
        homomorphism action Index component)
      (fun index => index.2.1)) :
    ((sourceRestrictedComponentFamilyActionIso homomorphism action Index
      component).inv.hom.hom point).2.1 = point.2.1 :=
  rfl

/-- Forgetting a copied-component index commutes with restriction along the
source group homomorphism. -/
theorem sourceRestrictedComponentFamilyProjection_naturality
    {source target : ProfiniteGrp.{u}}
    (homomorphism : source ⟶ target)
    (action : ContAction FintypeCat.{u} target)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent target action) :
    (sourceRestrictedComponentFamilyActionIso homomorphism action Index
          component).hom ≫
        sourceTemperoidComponentFamilyProjection source
          (sourceFiniteRestrictionAction homomorphism action)
          (SourceRestrictedComponentFamilyIndex
            homomorphism action Index component)
          (fun index => index.2.1) =
      (ContAction.res SourceCountableTypeCat homomorphism.hom).map
        (sourceTemperoidComponentFamilyProjection target action Index
          component) := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  rfl

end Iut
