/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceAnabelioidComponents
import Iut.Foundations.SourceTemperoid

/-!
# Countable families of finite-action components

A combinatorial covering of the semi-graph attached to a finite cover repeats
selected connected components of the finite constituent actions.  This file
constructs that repetition as a literal countable continuous action.

The group fixes the family index and acts inside the selected orbit.  Hence
the connected components of the resulting action are exactly the family
indices, including when the same finite orbit is selected more than once.
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

/-- An equivariant isomorphism of finite continuous actions transports their
orbit-component sets. -/
noncomputable def sourceFiniteActionComponentEquiv
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    (identification : first ≅ second) :
    SourceActionComponent G first ≃ SourceActionComponent G second := by
  let forward : SourceActionComponent G first →
      SourceActionComponent G second :=
    Quotient.map' identification.hom.hom.hom (by
      intro firstPoint secondPoint relation
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
      obtain ⟨element, equality⟩ := relation
      refine ⟨element, ?_⟩
      rw [← equality]
      have hnatural := (ConcreteCategory.congr_hom
        (identification.hom.hom.comm element) secondPoint).symm
      change
        element • identification.hom.hom.hom secondPoint =
          identification.hom.hom.hom (element • secondPoint) at hnatural
      exact hnatural)
  let reverse : SourceActionComponent G second →
      SourceActionComponent G first :=
    Quotient.map' identification.inv.hom.hom (by
      intro firstPoint secondPoint relation
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
      obtain ⟨element, equality⟩ := relation
      refine ⟨element, ?_⟩
      rw [← equality]
      have hnatural := (ConcreteCategory.congr_hom
        (identification.inv.hom.comm element) secondPoint).symm
      change
        element • identification.inv.hom.hom secondPoint =
          identification.inv.hom.hom (element • secondPoint) at hnatural
      exact hnatural)
  exact
    { toFun := forward
      invFun := reverse
      left_inv := by
        intro component
        induction component using Quotient.inductionOn' with
        | _ point =>
            apply congrArg Quotient.mk''
            have equality := congrArg
              (fun morphism : first ⟶ first ↦ morphism.hom.hom point)
              identification.hom_inv_id
            exact equality
      right_inv := by
        intro component
        induction component using Quotient.inductionOn' with
        | _ point =>
            apply congrArg Quotient.mk''
            have equality := congrArg
              (fun morphism : second ⟶ second ↦ morphism.hom.hom point)
              identification.inv_hom_id
            exact equality }

/-- The carrier obtained by taking one copy of the selected finite-action
component for every index in a countable family. -/
abbrev SourceTemperoidComponentFamilyCarrier
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (Index : Type u) (component : Index → SourceActionComponent G S) :=
  Σ index : Index, SourceActionComponentFiber G S (component index)

namespace SourceTemperoidComponentFamilyCarrier

variable
    (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G)
    (Index : Type u)
    (component : Index → SourceActionComponent G S)

noncomputable instance [Countable Index] : Countable
    (SourceTemperoidComponentFamilyCarrier G S Index component) :=
  inferInstance

noncomputable instance : SMul G
    (SourceTemperoidComponentFamilyCarrier G S Index component) where
  smul g point := ⟨point.1, g • point.2⟩

noncomputable instance : MulAction G
    (SourceTemperoidComponentFamilyCarrier G S Index component) where
  one_smul point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (one_smul G point.2)
  mul_smul first second point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (mul_smul first second point.2)

@[simp] theorem smul_fst
    (g : G)
    (point : SourceTemperoidComponentFamilyCarrier G S Index component) :
    (g • point).1 = point.1 :=
  rfl

@[simp] theorem smul_snd
    (g : G)
    (point : SourceTemperoidComponentFamilyCarrier G S Index component) :
    (g • point).2 = g • point.2 :=
  rfl

end SourceTemperoidComponentFamilyCarrier

/-- The countable continuous action obtained by repeating selected connected
components of a finite continuous action. -/
noncomputable def sourceTemperoidComponentFamilyAction
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent G S) :
    SourceTemperoidAction G := by
  let Carrier := SourceTemperoidComponentFamilyCarrier G S Index component
  let action : Action SourceCountableTypeCat.{u} G :=
    SourceCountableTypeCat.ofMulAction G
      (SourceCountableTypeCat.of Carrier)
  refine
    ⟨action, ?_⟩
  change ContinuousSMul G
    ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj action)
  letI : DiscreteTopology
      ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj action) :=
    ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro point
  change Carrier at point
  haveI : ContinuousSMul G S.obj.V := S.property
  have openPoint :
      IsOpen (MulAction.stabilizer G point.2.1 : Set G) :=
    stabilizer_isOpen G point.2.1
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G point.2.1)
    (H₂ := MulAction.stabilizer G point) _ openPoint
  intro g fixes
  rw [MulAction.mem_stabilizer_iff] at fixes ⊢
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact fixes

/-- Forget the copied-component index and include its underlying point back
into the original finite action. -/
noncomputable def sourceTemperoidComponentFamilyProjection
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent G S) :
    sourceTemperoidComponentFamilyAction G S Index component ⟶
      (SourceTemperoidAction.finiteInclusion G).obj S :=
  ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk (fun point => point.2.1)
      comm := fun element => by
        apply ConcreteCategory.hom_ext
        intro point
        rfl }

@[simp]
theorem sourceTemperoidComponentFamilyProjection_apply
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent G S)
    (point : SourceTemperoidComponentFamilyCarrier G S Index component) :
    (sourceTemperoidComponentFamilyProjection G S Index component).hom.hom
        point = point.2.1 :=
  rfl

/-- An equivariant finite-action isomorphism identifies the corresponding
selected orbit fibers. -/
noncomputable def sourceFiniteActionComponentFiberEquiv
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    (identification : first ≅ second)
    (firstComponent : SourceActionComponent G first)
    (secondComponent : SourceActionComponent G second)
    (componentCompatibility :
      sourceFiniteActionComponentEquiv identification firstComponent =
        secondComponent) :
    SourceActionComponentFiber G first firstComponent ≃
      SourceActionComponentFiber G second secondComponent where
  toFun point :=
    ⟨identification.hom.hom.hom point.1,
      by
        calc
          Quotient.mk'' (identification.hom.hom.hom point.1) =
              sourceFiniteActionComponentEquiv identification
                (Quotient.mk'' point.1) := rfl
          _ = sourceFiniteActionComponentEquiv identification
                firstComponent :=
            congrArg (sourceFiniteActionComponentEquiv identification)
              point.2
          _ = secondComponent := componentCompatibility⟩
  invFun point :=
    ⟨identification.inv.hom.hom point.1,
      by
        apply (sourceFiniteActionComponentEquiv identification).injective
        calc
          sourceFiniteActionComponentEquiv identification
              (Quotient.mk'' (identification.inv.hom.hom point.1)) =
              Quotient.mk'' point.1 := by
            apply congrArg Quotient.mk''
            have equality := congrArg
              (fun morphism : second ⟶ second ↦
                morphism.hom.hom point.1)
              identification.inv_hom_id
            exact equality
          _ = secondComponent := point.2
          _ = sourceFiniteActionComponentEquiv identification
              firstComponent := componentCompatibility.symm⟩
  left_inv point := by
    apply Subtype.ext
    have equality := congrArg
      (fun morphism : first ⟶ first ↦ morphism.hom.hom point.1)
      identification.hom_inv_id
    exact equality
  right_inv point := by
    apply Subtype.ext
    have equality := congrArg
      (fun morphism : second ⟶ second ↦ morphism.hom.hom point.1)
      identification.inv_hom_id
    exact equality

/-- Reindex a countable family of selected components through an equivariant
isomorphism of the underlying finite actions. -/
noncomputable def sourceTemperoidComponentFamilyCarrierEquiv
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    {FirstIndex SecondIndex : Type u}
    [Countable FirstIndex] [Countable SecondIndex]
    (identification : first ≅ second)
    (firstComponent : FirstIndex → SourceActionComponent G first)
    (secondComponent : SecondIndex → SourceActionComponent G second)
    (indexEquiv : FirstIndex ≃ SecondIndex)
    (componentCompatibility : ∀ index,
      sourceFiniteActionComponentEquiv identification
          (firstComponent index) =
        secondComponent (indexEquiv index)) :
    SourceTemperoidComponentFamilyCarrier
        G first FirstIndex firstComponent ≃
      SourceTemperoidComponentFamilyCarrier
        G second SecondIndex secondComponent :=
  Equiv.sigmaCongr indexEquiv fun index ↦
    sourceFiniteActionComponentFiberEquiv identification
      (firstComponent index) (secondComponent (indexEquiv index))
      (componentCompatibility index)

@[simp]
theorem sourceTemperoidComponentFamilyCarrierEquiv_apply_fst
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    {FirstIndex SecondIndex : Type u}
    [Countable FirstIndex] [Countable SecondIndex]
    (identification : first ≅ second)
    (firstComponent : FirstIndex → SourceActionComponent G first)
    (secondComponent : SecondIndex → SourceActionComponent G second)
    (indexEquiv : FirstIndex ≃ SecondIndex)
    (componentCompatibility : ∀ index,
      sourceFiniteActionComponentEquiv identification
          (firstComponent index) =
        secondComponent (indexEquiv index))
    (point : SourceTemperoidComponentFamilyCarrier
      G first FirstIndex firstComponent) :
    (sourceTemperoidComponentFamilyCarrierEquiv identification
      firstComponent secondComponent indexEquiv componentCompatibility
      point).1 = indexEquiv point.1 :=
  rfl

@[simp]
theorem sourceTemperoidComponentFamilyCarrierEquiv_apply_val
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    {FirstIndex SecondIndex : Type u}
    [Countable FirstIndex] [Countable SecondIndex]
    (identification : first ≅ second)
    (firstComponent : FirstIndex → SourceActionComponent G first)
    (secondComponent : SecondIndex → SourceActionComponent G second)
    (indexEquiv : FirstIndex ≃ SecondIndex)
    (componentCompatibility : ∀ index,
      sourceFiniteActionComponentEquiv identification
          (firstComponent index) =
        secondComponent (indexEquiv index))
    (point : SourceTemperoidComponentFamilyCarrier
      G first FirstIndex firstComponent) :
    (sourceTemperoidComponentFamilyCarrierEquiv identification
      firstComponent secondComponent indexEquiv componentCompatibility
      point).2.1 = identification.hom.hom.hom point.2.1 :=
  rfl

@[simp]
theorem sourceTemperoidComponentFamilyCarrierEquiv_symm_apply_val
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    {FirstIndex SecondIndex : Type u}
    [Countable FirstIndex] [Countable SecondIndex]
    (identification : first ≅ second)
    (firstComponent : FirstIndex → SourceActionComponent G first)
    (secondComponent : SecondIndex → SourceActionComponent G second)
    (indexEquiv : FirstIndex ≃ SecondIndex)
    (componentCompatibility : ∀ index,
      sourceFiniteActionComponentEquiv identification
          (firstComponent index) =
        secondComponent (indexEquiv index))
    (point : SourceTemperoidComponentFamilyCarrier
      G second SecondIndex secondComponent) :
    ((sourceTemperoidComponentFamilyCarrierEquiv identification
      firstComponent secondComponent indexEquiv componentCompatibility).symm
      point).2.1 = identification.inv.hom.hom point.2.1 :=
  by
    let carrierEquiv := sourceTemperoidComponentFamilyCarrierEquiv
      identification firstComponent secondComponent indexEquiv
        componentCompatibility
    let sourcePoint := carrierEquiv.symm point
    have forwardEquality :
        identification.hom.hom.hom sourcePoint.2.1 = point.2.1 := by
      have equality := congrArg (fun value => value.2.1)
        (carrierEquiv.apply_symm_apply point)
      simpa only [carrierEquiv, sourcePoint,
        sourceTemperoidComponentFamilyCarrierEquiv_apply_val] using equality
    have cancellation := congrArg
      (fun morphism : first ⟶ first => morphism.hom.hom sourcePoint.2.1)
      identification.hom_inv_id
    change sourcePoint.2.1 = identification.inv.hom.hom point.2.1
    calc
      sourcePoint.2.1 = identification.inv.hom.hom
          (identification.hom.hom.hom sourcePoint.2.1) := cancellation.symm
      _ = identification.inv.hom.hom point.2.1 :=
        congrArg identification.inv.hom.hom forwardEquality

/-- Reindexing compatible component copies is an isomorphism of countable
continuous actions, not merely a bijection of their carriers. -/
noncomputable def sourceTemperoidComponentFamilyActionIso
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    {FirstIndex SecondIndex : Type u}
    [Countable FirstIndex] [Countable SecondIndex]
    (identification : first ≅ second)
    (firstComponent : FirstIndex → SourceActionComponent G first)
    (secondComponent : SecondIndex → SourceActionComponent G second)
    (indexEquiv : FirstIndex ≃ SecondIndex)
    (componentCompatibility : ∀ index,
      sourceFiniteActionComponentEquiv identification
          (firstComponent index) =
        secondComponent (indexEquiv index)) :
    sourceTemperoidComponentFamilyAction
        G first FirstIndex firstComponent ≅
      sourceTemperoidComponentFamilyAction
        G second SecondIndex secondComponent := by
  let carrierEquiv :=
    sourceTemperoidComponentFamilyCarrierEquiv identification
      firstComponent secondComponent indexEquiv componentCompatibility
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk carrierEquiv
        inv := SourceCountableTypeCat.homMk carrierEquiv.symm
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro point
          change SourceTemperoidComponentFamilyCarrier
            G first FirstIndex firstComponent at point
          exact carrierEquiv.symm_apply_apply point
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro point
          change SourceTemperoidComponentFamilyCarrier
            G second SecondIndex secondComponent at point
          exact carrierEquiv.apply_symm_apply point }
  · intro g
    apply ConcreteCategory.hom_ext
    intro point
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      change
        identification.hom.hom.hom (g • point.2.1) =
          g • identification.hom.hom.hom point.2.1
      have hnatural := ConcreteCategory.congr_hom
        (identification.hom.hom.comm g) point.2.1
      change
        identification.hom.hom.hom (g • point.2.1) =
          g • identification.hom.hom.hom point.2.1 at hnatural
      exact hnatural

@[simp]
theorem sourceTemperoidComponentFamilyActionIso_hom_apply_val
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    {FirstIndex SecondIndex : Type u}
    [Countable FirstIndex] [Countable SecondIndex]
    (identification : first ≅ second)
    (firstComponent : FirstIndex → SourceActionComponent G first)
    (secondComponent : SecondIndex → SourceActionComponent G second)
    (indexEquiv : FirstIndex ≃ SecondIndex)
    (componentCompatibility : ∀ index,
      sourceFiniteActionComponentEquiv identification
          (firstComponent index) =
        secondComponent (indexEquiv index))
    (point : SourceTemperoidComponentFamilyCarrier
      G first FirstIndex firstComponent) :
    ((sourceTemperoidComponentFamilyActionIso identification firstComponent
      secondComponent indexEquiv componentCompatibility).hom.hom.hom
      point).2.1 = identification.hom.hom.hom point.2.1 :=
  rfl

@[simp]
theorem sourceTemperoidComponentFamilyActionIso_inv_apply_val
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    {FirstIndex SecondIndex : Type u}
    [Countable FirstIndex] [Countable SecondIndex]
    (identification : first ≅ second)
    (firstComponent : FirstIndex → SourceActionComponent G first)
    (secondComponent : SecondIndex → SourceActionComponent G second)
    (indexEquiv : FirstIndex ≃ SecondIndex)
    (componentCompatibility : ∀ index,
      sourceFiniteActionComponentEquiv identification
          (firstComponent index) =
        secondComponent (indexEquiv index))
    (point : SourceTemperoidComponentFamilyCarrier
      G second SecondIndex secondComponent) :
    ((sourceTemperoidComponentFamilyActionIso identification firstComponent
      secondComponent indexEquiv componentCompatibility).inv.hom.hom
      point).2.1 = identification.inv.hom.hom point.2.1 := by
  exact sourceTemperoidComponentFamilyCarrierEquiv_symm_apply_val
    identification firstComponent secondComponent indexEquiv
      componentCompatibility point

/-- Forgetting a copied-component index commutes with reindexing through an
equivariant isomorphism of the underlying finite actions. -/
theorem sourceTemperoidComponentFamilyProjection_naturality
    {G : ProfiniteGrp.{u}}
    {first second : ContAction FintypeCat.{u} G}
    {FirstIndex SecondIndex : Type u}
    [Countable FirstIndex] [Countable SecondIndex]
    (identification : first ≅ second)
    (firstComponent : FirstIndex → SourceActionComponent G first)
    (secondComponent : SecondIndex → SourceActionComponent G second)
    (indexEquiv : FirstIndex ≃ SecondIndex)
    (componentCompatibility : ∀ index,
      sourceFiniteActionComponentEquiv identification
          (firstComponent index) =
        secondComponent (indexEquiv index)) :
    (sourceTemperoidComponentFamilyActionIso identification firstComponent
          secondComponent indexEquiv componentCompatibility).hom ≫
        sourceTemperoidComponentFamilyProjection
          G second SecondIndex secondComponent =
      sourceTemperoidComponentFamilyProjection
          G first FirstIndex firstComponent ≫
        (SourceTemperoidAction.finiteInclusion G).map identification.hom := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  rfl

namespace SourceTemperoidComponentFamilyAction

variable
    (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G)
    (Index : Type u)
    (component : Index → SourceActionComponent G S)

/-- The group action never changes the family index. -/
@[simp] theorem smul_fst
    (g : G)
    (point : SourceTemperoidComponentFamilyCarrier G S Index component) :
    (g • point).1 = point.1 :=
  rfl

/-- A canonical point in each repeated component. -/
noncomputable def basePoint (index : Index) :
    SourceTemperoidComponentFamilyCarrier G S Index component :=
  ⟨index, component index |>.out,
    Quotient.out_eq' (component index)⟩

/-- Forget a point down to the index of its copied component. -/
def indexMap :
    SourceTemperoidComponentFamilyCarrier G S Index component → Index :=
  Sigma.fst

/-- The index map is constant on group orbits. -/
theorem indexMap_respects_orbit
    (first second :
      SourceTemperoidComponentFamilyCarrier G S Index component)
    (related : MulAction.orbitRel G _ first second) :
    indexMap G S Index component first =
      indexMap G S Index component second := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at related
  obtain ⟨g, equality⟩ := related
  exact (congrArg Sigma.fst equality).symm.trans
    (smul_fst G S Index component g second)

/-- The orbit quotient of the repeated action maps to its unchanged family
index. -/
noncomputable def componentToIndex :
    MulAction.orbitRel.Quotient G
        (SourceTemperoidComponentFamilyCarrier G S Index component) →
      Index :=
  fun orbit ↦ Quotient.liftOn' orbit (indexMap G S Index component)
    (indexMap_respects_orbit G S Index component)

/-- Insert a family index as the orbit of its canonical point. -/
noncomputable def indexToComponent :
    Index →
      MulAction.orbitRel.Quotient G
        (SourceTemperoidComponentFamilyCarrier G S Index component) :=
  fun index ↦ Quotient.mk'' (basePoint G S Index component index)

/-- The connected components of the repeated action are exactly its family
indices. -/
noncomputable def componentEquiv :
    MulAction.orbitRel.Quotient G
        (SourceTemperoidComponentFamilyCarrier G S Index component) ≃
      Index where
  toFun := componentToIndex G S Index component
  invFun := indexToComponent G S Index component
  left_inv := by
    intro orbit
    induction orbit using Quotient.inductionOn' with
    | _ point =>
        apply Quotient.sound
        change (basePoint G S Index component point.1) ∈
          MulAction.orbit G point
        rw [MulAction.mem_orbit_iff]
        have sameComponent :
            (component point.1).out ∈
              MulAction.orbit G point.2.1 := by
          rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
          exact (Quotient.out_eq' (component point.1)).trans point.2.2.symm
        obtain ⟨g, equality⟩ :=
          MulAction.mem_orbit_iff.mp sameComponent
        refine ⟨g, ?_⟩
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Subtype.ext
          exact equality
  right_inv := by
    intro index
    simp [componentToIndex, indexToComponent, indexMap, basePoint]

@[simp]
theorem componentEquiv_mk
    (point :
      SourceTemperoidComponentFamilyCarrier G S Index component) :
    componentEquiv G S Index component (Quotient.mk'' point) = point.1 :=
  by simp [componentEquiv, componentToIndex, indexMap]

@[simp]
theorem componentEquiv_symm_apply
    (index : Index) :
    (componentEquiv G S Index component).symm index =
      Quotient.mk'' (basePoint G S Index component index) :=
  rfl

end SourceTemperoidComponentFamilyAction

end Iut
