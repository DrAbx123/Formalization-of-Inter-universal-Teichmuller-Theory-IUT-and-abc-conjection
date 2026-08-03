/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedActionFactorization

/-!
# Orbit decomposition of countable temperoid actions

The corrected form of *Semi-graphs of Anabelioids*, Definition 3.5(ii),
allows each connected component to choose its own finite splitting level.
On the action side, those connected components are the orbits of a countable
continuous action.  This file constructs each orbit as a connected temperoid
object and proves that the countable coproduct of the orbit fibers recovers
the original action.

For an action of a tempered inverse-limit group, the existing connected
factorization theorem can then be applied independently to every orbit.
-/

namespace Iut

universe u v w

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

/-! ## Orbit fibers -/

/-- The orbit set of a countable continuous action. -/
abbrev SourceTemperoidOrbit
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G) : Type u :=
  MulAction.orbitRel.Quotient G object.obj.V.obj

noncomputable instance sourceTemperoidOrbitCountable
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G) :
    Countable (SourceTemperoidOrbit G object) :=
  inferInstance

/-- The points lying in one selected orbit. -/
abbrev SourceTemperoidOrbitFiber
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object) : Type u :=
  { point : object.obj.V.obj // Quotient.mk'' point = orbit }

namespace SourceTemperoidOrbitFiber

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object)

noncomputable instance : Countable (SourceTemperoidOrbitFiber G object orbit) :=
  Subtype.countable

noncomputable instance : SMul G (SourceTemperoidOrbitFiber G object orbit) where
  smul element point :=
    ⟨element • point.1, by
      have sameOrbit :
          (Quotient.mk'' (element • point.1) : SourceTemperoidOrbit G object) =
            Quotient.mk'' point.1 :=
        Quotient.sound
          ((MulAction.orbitRel_apply).2
            (MulAction.mem_orbit point.1 element))
      exact sameOrbit.trans point.2⟩

noncomputable instance : MulAction G
    (SourceTemperoidOrbitFiber G object orbit) where
  one_smul point := by
    apply Subtype.ext
    exact one_smul G point.1
  mul_smul first second point := by
    apply Subtype.ext
    exact mul_smul first second point.1

@[simp]
theorem smul_val (element : G)
    (point : SourceTemperoidOrbitFiber G object orbit) :
    (element • point).1 = element • point.1 :=
  rfl

end SourceTemperoidOrbitFiber

/-- One orbit, equipped with its inherited continuous action. -/
noncomputable def sourceTemperoidOrbitAction
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object) :
    SourceTemperoidAction.{u, v} G := by
  let Carrier := SourceTemperoidOrbitFiber G object orbit
  let action : Action SourceCountableTypeCat.{u} G :=
    SourceCountableTypeCat.ofMulAction G (SourceCountableTypeCat.of Carrier)
  refine ⟨action, ?_⟩
  change ContinuousSMul G
    ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj action)
  letI : DiscreteTopology
      ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj action) :=
    ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro point
  have openUnderlying :
      IsOpen (MulAction.stabilizer G point.1 : Set G) :=
    stabilizer_isOpen G point.1
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G point.1)
    (H₂ := MulAction.stabilizer G point) _ openUnderlying
  intro element fixes
  rw [MulAction.mem_stabilizer_iff] at fixes ⊢
  apply Subtype.ext
  exact fixes

/-- The selected orbit is nonempty, represented canonically by `orbit.out`. -/
noncomputable instance sourceTemperoidOrbitFiberNonempty
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object) :
    Nonempty (SourceTemperoidOrbitFiber G object orbit) :=
  ⟨⟨orbit.out, Quotient.out_eq' orbit⟩⟩

/-- Every orbit action is transitive. -/
theorem sourceTemperoidOrbitAction_pretransitive
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object) :
    MulAction.IsPretransitive G
      (sourceTemperoidOrbitAction G object orbit).obj.V.obj := by
  constructor
  intro first second
  have sameOrbit : second.1 ∈ MulAction.orbit G first.1 := by
    rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
    exact second.2.trans first.2.symm
  obtain ⟨element, maps⟩ := MulAction.mem_orbit_iff.mp sameOrbit
  refine ⟨element, ?_⟩
  apply Subtype.ext
  exact maps

/-- One orbit as an object of the connected temperoid. -/
noncomputable def sourceConnectedTemperoidOrbit
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object) :
    SourceConnectedTemperoid.{u, v} G :=
  ⟨sourceTemperoidOrbitAction G object orbit,
    ⟨⟨⟨orbit.out, Quotient.out_eq' orbit⟩⟩,
      sourceTemperoidOrbitAction_pretransitive G object orbit⟩⟩

/-- Include one orbit fiber into the original action. -/
noncomputable def sourceTemperoidOrbitInclusion
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object) :
    sourceTemperoidOrbitAction G object orbit ⟶ object :=
  ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk Subtype.val
      comm := fun _ ↦ by
        apply ConcreteCategory.hom_ext
        intro point
        rfl }

@[simp]
theorem sourceTemperoidOrbitInclusion_apply
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object)
    (point : SourceTemperoidOrbitFiber G object orbit) :
    (sourceTemperoidOrbitInclusion G object orbit).hom.hom point = point.1 :=
  rfl

/-! ## Countable reconstruction -/

/-- The disjoint union of all orbit fibers of an action. -/
abbrev SourceTemperoidOrbitDecompositionCarrier
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G) : Type u :=
  Σ orbit : SourceTemperoidOrbit G object,
    SourceTemperoidOrbitFiber G object orbit

namespace SourceTemperoidOrbitDecompositionCarrier

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)

noncomputable instance : Countable
    (SourceTemperoidOrbitDecompositionCarrier G object) :=
  inferInstance

noncomputable instance : SMul G
    (SourceTemperoidOrbitDecompositionCarrier G object) where
  smul element point := ⟨point.1, element • point.2⟩

noncomputable instance : MulAction G
    (SourceTemperoidOrbitDecompositionCarrier G object) where
  one_smul point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (one_smul G point.2)
  mul_smul first second point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (mul_smul first second point.2)

@[simp]
theorem smul_fst (element : G)
    (point : SourceTemperoidOrbitDecompositionCarrier G object) :
    (element • point).1 = point.1 :=
  rfl

@[simp]
theorem smul_val (element : G)
    (point : SourceTemperoidOrbitDecompositionCarrier G object) :
    (element • point).2.1 = element • point.2.1 :=
  rfl

end SourceTemperoidOrbitDecompositionCarrier

/-- The continuous action on the disjoint union of all orbit fibers. -/
noncomputable def sourceTemperoidOrbitDecompositionAction
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G) :
    SourceTemperoidAction.{u, v} G := by
  let Carrier := SourceTemperoidOrbitDecompositionCarrier G object
  let action : Action SourceCountableTypeCat.{u} G :=
    SourceCountableTypeCat.ofMulAction G (SourceCountableTypeCat.of Carrier)
  refine ⟨action, ?_⟩
  change ContinuousSMul G
    ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj action)
  letI : DiscreteTopology
      ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj action) :=
    ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro point
  have openUnderlying :
      IsOpen (MulAction.stabilizer G point.2.1 : Set G) :=
    stabilizer_isOpen G point.2.1
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G point.2.1)
    (H₂ := MulAction.stabilizer G point) _ openUnderlying
  intro element fixes
  rw [MulAction.mem_stabilizer_iff] at fixes ⊢
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact fixes

/-- Forgetting the orbit tag is a bijection onto the original carrier. -/
noncomputable def sourceTemperoidOrbitDecompositionCarrierEquiv
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G) :
    SourceTemperoidOrbitDecompositionCarrier G object ≃ object.obj.V.obj :=
  Equiv.sigmaFiberEquiv
    (fun point : object.obj.V.obj ↦
      (Quotient.mk'' point : SourceTemperoidOrbit G object))

@[simp]
theorem sourceTemperoidOrbitDecompositionCarrierEquiv_apply
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (point : SourceTemperoidOrbitDecompositionCarrier G object) :
    sourceTemperoidOrbitDecompositionCarrierEquiv G object point = point.2.1 :=
  rfl

/-- The coproduct of all orbit actions is canonically the original action. -/
noncomputable def sourceTemperoidOrbitDecompositionIso
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G) :
    sourceTemperoidOrbitDecompositionAction G object ≅ object := by
  let carrierEquiv := sourceTemperoidOrbitDecompositionCarrierEquiv G object
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
    rfl

/-- Assemble a family of orbitwise equivariant maps into a map from the
explicit orbit decomposition to a target action. -/
noncomputable def sourceTemperoidOrbitDecompositionMap
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (source target : SourceTemperoidAction.{u, v} G)
    (targetOrbit : SourceTemperoidOrbit G source →
      SourceTemperoidOrbit G target)
    (componentMap : ∀ orbit,
      sourceTemperoidOrbitAction G source orbit ⟶
        sourceTemperoidOrbitAction G target (targetOrbit orbit)) :
    sourceTemperoidOrbitDecompositionAction G source ⟶ target := by
  apply ObjectProperty.homMk
  refine
    { hom := SourceCountableTypeCat.homMk (fun point ↦
        ((componentMap point.1).hom.hom point.2).1)
      comm := ?_ }
  intro element
  apply ConcreteCategory.hom_ext
  intro point
  exact congrArg Subtype.val <|
    ConcreteCategory.congr_hom ((componentMap point.1).hom.comm element)
      point.2

/-! ## Functoriality of orbit indices -/

/-- An equivariant map sends an orbit to the orbit containing its image. -/
noncomputable def sourceTemperoidOrbitMap
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {source target : SourceTemperoidAction.{u, v} G}
    (map : source ⟶ target) :
    SourceTemperoidOrbit G source → SourceTemperoidOrbit G target :=
  Quotient.map' map.hom.hom (by
    intro first second related
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at related ⊢
    obtain ⟨element, maps⟩ := related
    refine ⟨element, ?_⟩
    rw [← maps]
    exact (ConcreteCategory.congr_hom
      (map.hom.comm element) second).symm)

@[simp]
theorem sourceTemperoidOrbitMap_mk
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {source target : SourceTemperoidAction.{u, v} G}
    (map : source ⟶ target) (point : source.obj.V.obj) :
    sourceTemperoidOrbitMap map (Quotient.mk'' point) =
      Quotient.mk'' (map.hom.hom point) :=
  rfl

/-- The identity morphism induces the identity map on orbit indices. -/
@[simp]
theorem sourceTemperoidOrbitMap_id
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction.{u, v} G)
    (orbit : SourceTemperoidOrbit G object) :
    sourceTemperoidOrbitMap (𝟙 object) orbit = orbit := by
  induction orbit using Quotient.inductionOn' with
  | _ point => rfl

/-- The restriction of an equivariant map to one orbit fiber. -/
noncomputable def sourceTemperoidOrbitFiberMap
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {source target : SourceTemperoidAction.{u, v} G}
    (map : source ⟶ target) (orbit : SourceTemperoidOrbit G source) :
    sourceTemperoidOrbitAction G source orbit ⟶
      sourceTemperoidOrbitAction G target (sourceTemperoidOrbitMap map orbit) :=
  ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk (fun point ↦
        ⟨map.hom.hom point.1, by
          calc
            Quotient.mk'' (map.hom.hom point.1) =
                sourceTemperoidOrbitMap map (Quotient.mk'' point.1) := rfl
            _ = sourceTemperoidOrbitMap map orbit :=
              congrArg (sourceTemperoidOrbitMap map) point.2⟩)
      comm := fun element ↦ by
        apply ConcreteCategory.hom_ext
        intro point
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (map.hom.comm element) point.1 }

@[simp]
theorem sourceTemperoidOrbitFiberMap_apply
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {source target : SourceTemperoidAction.{u, v} G}
    (map : source ⟶ target) (orbit : SourceTemperoidOrbit G source)
    (point : SourceTemperoidOrbitFiber G source orbit) :
    ((sourceTemperoidOrbitFiberMap map orbit).hom.hom point).1 =
      map.hom.hom point.1 :=
  rfl

/-- The restricted orbit map as a morphism of connected temperoid objects. -/
noncomputable def sourceConnectedTemperoidOrbitMap
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {source target : SourceTemperoidAction.{u, v} G}
    (map : source ⟶ target) (orbit : SourceTemperoidOrbit G source) :
    sourceConnectedTemperoidOrbit G source orbit ⟶
      sourceConnectedTemperoidOrbit G target
        (sourceTemperoidOrbitMap map orbit) :=
  ObjectProperty.homMk (sourceTemperoidOrbitFiberMap map orbit)

/-- An equivariant map is surjective from every source orbit onto the target
orbit containing its image. -/
theorem sourceTemperoidOrbitFiberMap_surjective
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {source target : SourceTemperoidAction.{u, v} G}
    (map : source ⟶ target) (orbit : SourceTemperoidOrbit G source) :
    Function.Surjective
      (sourceTemperoidOrbitFiberMap map orbit).hom.hom :=
  SourceConnectedTemperoid.hom_surjective G
    (sourceConnectedTemperoidOrbit G source orbit)
    (sourceConnectedTemperoidOrbit G target
      (sourceTemperoidOrbitMap map orbit))
    (sourceConnectedTemperoidOrbitMap map orbit)

/-- Orbit-index maps respect composition. -/
theorem sourceTemperoidOrbitMap_comp
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second third : SourceTemperoidAction.{u, v} G}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (orbit : SourceTemperoidOrbit G first) :
    sourceTemperoidOrbitMap (firstMap ≫ secondMap) orbit =
      sourceTemperoidOrbitMap secondMap
        (sourceTemperoidOrbitMap firstMap orbit) := by
  induction orbit using Quotient.inductionOn' with
  | _ point => rfl

/-! ## Componentwise inverse-limit descent -/

namespace SourceTemperedGroupPresentation

variable {Index : Type v} [Category.{w} Index]
    (system : SourceTemperedGroupPresentation Index)

/-- Every orbit of an inverse-limit action independently descends to one
discrete coordinate when the literal coordinate maps are surjective. -/
noncomputable def orbitLevelFactorization
    [IsCofiltered Index]
    (projectionSurjective : ∀ level,
      Function.Surjective (system.projection level))
    (object : SourceTemperoidAction.{u, max v w} system.Limit)
    (orbit : SourceTemperoidOrbit system.Limit object) :
    system.ConnectedActionLevelFactorization
      (sourceConnectedTemperoidOrbit system.Limit object orbit) :=
  system.connectedActionLevelFactorization projectionSurjective
    (sourceConnectedTemperoidOrbit system.Limit object orbit)

end SourceTemperedGroupPresentation

end Iut
