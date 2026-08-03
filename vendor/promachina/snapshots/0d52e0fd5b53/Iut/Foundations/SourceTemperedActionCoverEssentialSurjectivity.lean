/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedActionCoverEquivalence

/-!
# Essential surjectivity of the tempered action-cover functor

This file completes the object-level half of *Semi-graphs of Anabelioids*,
Proposition 3.6(ii), with the May 2020 correction to Definition 3.5(ii).
For every intrinsic connected component of a geometric tempered cover, its
independently selected finite-level deck action is pulled back to the literal
inverse-limit group.  Their countable disjoint union is then transported to
the declared tempered deck group.

No common finite level is selected for the complete cover.
-/

namespace Iut

universe u v

open CategoryTheory
open scoped CategoryTheory SourceCountableTypeCatDiscrete

/-! ## Countable families of connected actions -/

/-- The carrier of a countable family of connected actions of one group. -/
abbrev SourceTemperoidConnectedFamilyCarrier
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Index : Type u)
    (family : Index → SourceConnectedTemperoid.{u, v} G) :=
  Σ index : Index, (family index).obj.obj.V.obj

namespace SourceTemperoidConnectedFamilyCarrier

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (Index : Type u)
variable (family : Index → SourceConnectedTemperoid.{u, v} G)

noncomputable instance [Countable Index] :
    Countable (SourceTemperoidConnectedFamilyCarrier G Index family) :=
  inferInstance

noncomputable instance :
    SMul G (SourceTemperoidConnectedFamilyCarrier G Index family) where
  smul element point := ⟨point.1, element • point.2⟩

noncomputable instance :
    MulAction G (SourceTemperoidConnectedFamilyCarrier G Index family) where
  one_smul point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (one_smul G point.2)
  mul_smul first second point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (mul_smul first second point.2)

@[simp] theorem smul_fst
    (element : G)
    (point : SourceTemperoidConnectedFamilyCarrier G Index family) :
    (element • point).1 = point.1 :=
  rfl

@[simp] theorem smul_snd
    (element : G)
    (point : SourceTemperoidConnectedFamilyCarrier G Index family) :
    (element • point).2 = element • point.2 :=
  rfl

end SourceTemperoidConnectedFamilyCarrier

/-- The continuous action obtained by taking the disjoint union of a
countable family of connected continuous actions. -/
noncomputable def sourceTemperoidConnectedFamilyAction
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Index : Type u) [Countable Index]
    (family : Index → SourceConnectedTemperoid.{u, v} G) :
    SourceTemperoidAction.{u, v} G := by
  let Carrier := SourceTemperoidConnectedFamilyCarrier G Index family
  let action : Action SourceCountableTypeCat.{u} G :=
    SourceCountableTypeCat.ofMulAction G (SourceCountableTypeCat.of Carrier)
  refine ⟨action, ?_⟩
  change ContinuousSMul G
    ((CategoryTheory.forget₂
      (Action SourceCountableTypeCat.{u} G) TopCat).obj action)
  letI : DiscreteTopology
      ((CategoryTheory.forget₂
        (Action SourceCountableTypeCat.{u} G) TopCat).obj action) :=
    ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro point
  have openPoint : IsOpen
      (MulAction.stabilizer G point.2 : Set G) :=
    stabilizer_isOpen G point.2
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G point.2)
    (H₂ := MulAction.stabilizer G point) _ openPoint
  intro element fixes
  rw [MulAction.mem_stabilizer_iff] at fixes ⊢
  apply Sigma.ext
  · rfl
  · exact heq_of_eq fixes

/-- The orbits of a disjoint family of connected actions are exactly its
family indices. -/
noncomputable def sourceTemperoidConnectedFamilyOrbitEquiv
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Index : Type u) [Countable Index]
    (family : Index → SourceConnectedTemperoid.{u, v} G) :
    SourceTemperoidOrbit G
        (sourceTemperoidConnectedFamilyAction G Index family) ≃ Index where
  toFun := Quotient.lift Sigma.fst (by
    intro first second related
    change MulAction.orbitRel G
      (SourceTemperoidConnectedFamilyCarrier G Index family)
      first second at related
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at related
    obtain ⟨element, rfl⟩ := related
    rfl)
  invFun := fun index ↦ Quotient.mk''
    (⟨index, Classical.choice (family index).property.1⟩ :
      SourceTemperoidConnectedFamilyCarrier G Index family)
  left_inv := by
    intro orbit
    induction orbit using Quotient.inductionOn' with
    | _ point =>
        apply Quotient.sound
        change MulAction.orbitRel G
          (SourceTemperoidConnectedFamilyCarrier G Index family)
          ⟨point.1, Classical.choice (family point.1).property.1⟩ point
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        obtain ⟨element, maps⟩ :=
          (family point.1).property.2.exists_smul_eq
            point.2 (Classical.choice (family point.1).property.1)
        refine ⟨element, ?_⟩
        apply Sigma.ext
        · rfl
        · exact heq_of_eq maps
  right_inv := by
    intro index
    rfl

@[simp]
theorem sourceTemperoidConnectedFamilyOrbitEquiv_mk
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Index : Type u) [Countable Index]
    (family : Index → SourceConnectedTemperoid.{u, v} G)
    (point : SourceTemperoidConnectedFamilyCarrier G Index family) :
    sourceTemperoidConnectedFamilyOrbitEquiv G Index family
        (Quotient.mk'' point) = point.1 :=
  rfl

/-- Transport between equal family indices commutes with the common group
action. -/
theorem sourceTemperoidConnectedFamily_cast_smul
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Index : Type u)
    (family : Index → SourceConnectedTemperoid.{u, v} G)
    {first second : Index} (equality : first = second)
    (element : G) (point : (family first).obj.obj.V.obj) :
    cast (congrArg (fun index ↦ (family index).obj.obj.V.obj) equality)
        (element • point) =
      element • cast
        (congrArg (fun index ↦ (family index).obj.obj.V.obj) equality) point := by
  cases equality
  rfl

/-- Forget the orbit-fiber wrapper and cast the family member to the unique
index represented by the orbit. -/
noncomputable def sourceTemperoidConnectedFamilyOrbitProjection
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Index : Type u) [Countable Index]
    (family : Index → SourceConnectedTemperoid.{u, v} G)
    (orbit : SourceTemperoidOrbit G
      (sourceTemperoidConnectedFamilyAction G Index family)) :
    SourceTemperoidOrbitFiber G
        (sourceTemperoidConnectedFamilyAction G Index family) orbit →
      (family (sourceTemperoidConnectedFamilyOrbitEquiv
        G Index family orbit)).obj.obj.V.obj :=
  fun point ↦ cast
    (congrArg
      (fun index ↦ (family index).obj.obj.V.obj)
      (congrArg
        (sourceTemperoidConnectedFamilyOrbitEquiv G Index family)
        point.2))
    point.1.2

/-- The orbit projection is equivariant. -/
theorem sourceTemperoidConnectedFamilyOrbitProjection_smul
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Index : Type u) [Countable Index]
    (family : Index → SourceConnectedTemperoid.{u, v} G)
    (orbit : SourceTemperoidOrbit G
      (sourceTemperoidConnectedFamilyAction G Index family))
    (element : G)
    (point : SourceTemperoidOrbitFiber G
      (sourceTemperoidConnectedFamilyAction G Index family) orbit) :
    sourceTemperoidConnectedFamilyOrbitProjection G Index family orbit
        (element • point) =
      element • sourceTemperoidConnectedFamilyOrbitProjection
        G Index family orbit point := by
  unfold sourceTemperoidConnectedFamilyOrbitProjection
  let indexEquiv := sourceTemperoidConnectedFamilyOrbitEquiv G Index family
  let indexEquality := congrArg indexEquiv point.2
  let smulIndexEquality := congrArg indexEquiv (element • point).2
  have equality : smulIndexEquality = indexEquality := Subsingleton.elim _ _
  change cast
      (congrArg (fun index ↦ (family index).obj.obj.V.obj)
        smulIndexEquality)
        (element • point.1.2) =
    element • cast
      (congrArg (fun index ↦ (family index).obj.obj.V.obj)
        indexEquality) point.1.2
  rw [equality]
  exact sourceTemperoidConnectedFamily_cast_smul
    G Index family indexEquality element point.1.2

/-- Projection identifies one orbit of the family action with its unique
connected member. -/
noncomputable def sourceTemperoidConnectedFamilyOrbitIso
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Index : Type u) [Countable Index]
    (family : Index → SourceConnectedTemperoid.{u, v} G)
    (orbit : SourceTemperoidOrbit G
      (sourceTemperoidConnectedFamilyAction G Index family)) :
    sourceTemperoidOrbitAction G
        (sourceTemperoidConnectedFamilyAction G Index family) orbit ≅
      (family (sourceTemperoidConnectedFamilyOrbitEquiv
        G Index family orbit)).obj := by
  let projection := sourceTemperoidConnectedFamilyOrbitProjection
    G Index family orbit
  have projectionInjective : Function.Injective projection := by
    intro first second equality
    apply Subtype.ext
    let indexEquiv := sourceTemperoidConnectedFamilyOrbitEquiv G Index family
    have firstIndex : first.1.1 = indexEquiv orbit :=
      congrArg indexEquiv first.2
    have secondIndex : second.1.1 = indexEquiv orbit :=
      congrArg indexEquiv second.2
    apply Sigma.ext (firstIndex.trans secondIndex.symm)
    let firstCast := congrArg
      (fun index ↦ (family index).obj.obj.V.obj) firstIndex
    let secondCast := congrArg
      (fun index ↦ (family index).obj.obj.V.obj) secondIndex
    exact (cast_heq firstCast first.1.2).symm.trans <|
      (heq_of_eq equality).trans (cast_heq secondCast second.1.2)
  have projectionSurjective : Function.Surjective projection := by
    intro target
    let indexEquiv := sourceTemperoidConnectedFamilyOrbitEquiv G Index family
    let point : SourceTemperoidConnectedFamilyCarrier G Index family :=
      ⟨indexEquiv orbit, target⟩
    have pointOrbit :
        (Quotient.mk'' point : SourceTemperoidOrbit G
          (sourceTemperoidConnectedFamilyAction G Index family)) = orbit := by
      apply indexEquiv.injective
      rfl
    refine ⟨⟨point, pointOrbit⟩, ?_⟩
    unfold projection sourceTemperoidConnectedFamilyOrbitProjection
    exact eq_of_heq (cast_heq _ target)
  let carrierEquiv := Equiv.ofBijective projection
    ⟨projectionInjective, projectionSurjective⟩
  apply CategoryTheory.ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk carrierEquiv
        inv := SourceCountableTypeCat.homMk carrierEquiv.symm
        hom_inv_id := by
          apply CategoryTheory.ConcreteCategory.hom_ext
          intro point
          exact carrierEquiv.symm_apply_apply point
        inv_hom_id := by
          apply CategoryTheory.ConcreteCategory.hom_ext
          intro point
          exact carrierEquiv.apply_symm_apply point }
  · intro element
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro point
    exact sourceTemperoidConnectedFamilyOrbitProjection_smul
      G Index family orbit element point

/-- An equivariant isomorphism identifies the orbit sets of two continuous
actions. -/
noncomputable def sourceTemperoidOrbitEquivOfIso
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second : SourceTemperoidAction.{u, v} G}
    (identification : first ≅ second) :
    SourceTemperoidOrbit G first ≃ SourceTemperoidOrbit G second where
  toFun := sourceTemperoidOrbitMap identification.hom
  invFun := sourceTemperoidOrbitMap identification.inv
  left_inv := by
    intro orbit
    induction orbit using Quotient.inductionOn' with
    | _ point =>
        apply congrArg Quotient.mk''
        exact congrArg
          (fun morphism : first ⟶ first ↦ morphism.hom.hom point)
          identification.hom_inv_id
  right_inv := by
    intro orbit
    induction orbit using Quotient.inductionOn' with
    | _ point =>
        apply congrArg Quotient.mk''
        exact congrArg
          (fun morphism : second ⟶ second ↦ morphism.hom.hom point)
          identification.inv_hom_id

/-- Restricting an equivariant isomorphism to one orbit gives an isomorphism
onto the corresponding target orbit. -/
noncomputable def sourceTemperoidOrbitIsoOfIso
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second : SourceTemperoidAction.{u, v} G}
    (identification : first ≅ second)
    (orbit : SourceTemperoidOrbit G first) :
    sourceTemperoidOrbitAction G first orbit ≅
      sourceTemperoidOrbitAction G second
        (sourceTemperoidOrbitMap identification.hom orbit) := by
  let restricted := sourceTemperoidOrbitFiberMap identification.hom orbit
  have injective : Function.Injective restricted.hom.hom := by
    intro firstPoint secondPoint equality
    apply Subtype.ext
    let mappedEquality := congrArg Subtype.val equality
    calc
      firstPoint.1 = identification.inv.hom.hom
          (identification.hom.hom firstPoint.1) := by
        symm
        exact congrArg
          (fun morphism : first ⟶ first ↦ morphism.hom.hom firstPoint.1)
          identification.hom_inv_id
      _ = identification.inv.hom.hom
          (identification.hom.hom secondPoint.1) :=
        congrArg identification.inv.hom.hom mappedEquality
      _ = secondPoint.1 :=
        congrArg
          (fun morphism : first ⟶ first ↦ morphism.hom.hom secondPoint.1)
          identification.hom_inv_id
  have bijective : Function.Bijective restricted.hom.hom :=
    ⟨injective,
      sourceTemperoidOrbitFiberMap_surjective identification.hom orbit⟩
  let carrierEquiv := Equiv.ofBijective restricted.hom.hom bijective
  apply CategoryTheory.ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk carrierEquiv
        inv := SourceCountableTypeCat.homMk carrierEquiv.symm
        hom_inv_id := by
          apply CategoryTheory.ConcreteCategory.hom_ext
          intro point
          exact carrierEquiv.symm_apply_apply point
        inv_hom_id := by
          apply CategoryTheory.ConcreteCategory.hom_ext
          intro point
          exact carrierEquiv.apply_symm_apply point }
  · intro element
    exact restricted.hom.comm element

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

open SourceSemiGraphOfAnabelioids.GluedObject
open SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]

/-! ## The component-indexed inverse-limit action -/

/-- The finite deck action selected by the corrected tempered classification
of one intrinsic geometric component. -/
noncomputable def classifiedComponentAction
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (component : GeometricComponent source) :
    SourceConnectedTemperoid
      (DeckGroup diagram root
        (componentwiseTemperedClassification
          diagram root source tempered component).1) :=
  (componentwiseTemperedClassification
    diagram root source tempered component).2.1

/-- The selected component action with the universe lift used by the literal
inverse-limit presentation restored. -/
noncomputable def classifiedComponentLevelAction
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (component : GeometricComponent source) :
    SourceConnectedTemperoid.{u, u + 1}
      ((literalTemperedPresentation diagram root).DiscreteLevel
        (componentwiseTemperedClassification
          diagram root source tempered component).1) :=
  sourceConnectedTemperoidResEquivInverse
    (deckULiftContinuousMulEquiv diagram root
      (componentwiseTemperedClassification
        diagram root source tempered component).1).symm
    (classifiedComponentAction diagram root source tempered component)

/-- Pulling a connected action back along a surjective continuous group map
preserves connectedness. -/
noncomputable def sourceConnectedTemperoidResOfSurjective
    {G : Type v} {H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (homomorphism : G →ₜ* H) (surjective : Function.Surjective homomorphism)
    (object : SourceConnectedTemperoid.{u, _} H) :
    SourceConnectedTemperoid.{u, v} G := by
  let restricted := (ContAction.res SourceCountableTypeCat homomorphism).obj
    object.obj
  refine ⟨restricted, ⟨object.property.1, ?_⟩⟩
  constructor
  intro first second
  obtain ⟨element, maps⟩ := object.property.2.exists_smul_eq first second
  obtain ⟨lift, rfl⟩ := surjective element
  exact ⟨lift, maps⟩

/-- The connected action selected for one component, pulled back to the
literal inverse-limit deck group. -/
noncomputable def classifiedComponentLimitAction
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (component : GeometricComponent source) :
    SourceConnectedTemperoid.{u, u + 1}
      (literalTemperedPresentation diagram root).Limit :=
  sourceConnectedTemperoidResOfSurjective
    ((literalTemperedPresentation diagram root).continuousProjection
      (componentwiseTemperedClassification
        diagram root source tempered component).1)
    (literalTemperedPresentation_projection_surjective diagram root
      (componentwiseTemperedClassification
        diagram root source tempered component).1)
    (classifiedComponentLevelAction diagram root source tempered component)

/-- The literal inverse-limit action obtained by taking one connected orbit
for every intrinsic component of the geometric cover. -/
noncomputable def classifiedCoverLiteralAction
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source) :
    SourceTemperoidAction.{u, u + 1}
      (literalTemperedPresentation diagram root).Limit :=
  sourceTemperoidConnectedFamilyAction
    (literalTemperedPresentation diagram root).Limit
    (GeometricComponent source)
    (classifiedComponentLimitAction diagram root source tempered)

/-- The action of the declared tempered deck group reconstructed from a
corrected componentwise tempered cover. -/
noncomputable def classifiedCoverAction
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source) :
    SourceTemperoidAction.{u, u + 1} (TemperedDeckGroup diagram root) :=
  (literalLimitActionEquivalence diagram root).inverse.obj
    (classifiedCoverLiteralAction diagram root source tempered)

/-- The orbits of the reconstructed action are canonically the intrinsic
geometric components from which it was assembled. -/
noncomputable def classifiedCoverOrbitComponentEquiv
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source) :
    SourceTemperoidOrbit
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root
          (classifiedCoverAction diagram root source tempered)) ≃
      GeometricComponent source :=
  (sourceTemperoidOrbitEquivOfIso
    ((literalLimitActionEquivalence diagram root).counitIso.app
      (classifiedCoverLiteralAction diagram root source tempered))).trans
    (sourceTemperoidConnectedFamilyOrbitEquiv
      (literalTemperedPresentation diagram root).Limit
      (GeometricComponent source)
      (classifiedComponentLimitAction diagram root source tempered))

/-- On each orbit, the round-trip action-category equivalence followed by
the family-orbit projection identifies the orbit with the independently
selected component action. -/
noncomputable def classifiedCoverOrbitLimitIso
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root
        (classifiedCoverAction diagram root source tempered))) :
    sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root
          (classifiedCoverAction diagram root source tempered)) orbit ≅
      (classifiedComponentLimitAction diagram root source tempered
        (classifiedCoverOrbitComponentEquiv
          diagram root source tempered orbit)).obj := by
  let family := classifiedCoverLiteralAction diagram root source tempered
  let roundtrip :=
    (literalLimitActionEquivalence diagram root).counitIso.app family
  let familyOrbit := sourceTemperoidOrbitMap roundtrip.hom orbit
  exact
    (sourceTemperoidOrbitIsoOfIso roundtrip orbit).trans
      (sourceTemperoidConnectedFamilyOrbitIso
        (literalTemperedPresentation diagram root).Limit
        (GeometricComponent source)
        (classifiedComponentLimitAction diagram root source tempered)
        familyOrbit)

/-- The arbitrary level selected by inverse-limit factorization and the
component's original classified level admit a common refinement. -/
noncomputable def classifiedOrbitCommonLevel
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root
        (classifiedCoverAction diagram root source tempered))) :
    GaloisLevel diagram root :=
  CategoryTheory.IsCofiltered.min
    (literalOrbitLevelFactorization diagram root
      (classifiedCoverAction diagram root source tempered) orbit).level
    (componentwiseTemperedClassification diagram root source tempered
      (classifiedCoverOrbitComponentEquiv
        diagram root source tempered orbit)).1

/-- The common level refines the factorization level chosen for the action
orbit. -/
noncomputable def classifiedOrbitCommonToAction
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root
        (classifiedCoverAction diagram root source tempered))) :
    classifiedOrbitCommonLevel diagram root source tempered orbit ⟶
      (literalOrbitLevelFactorization diagram root
        (classifiedCoverAction diagram root source tempered) orbit).level :=
  CategoryTheory.IsCofiltered.minToLeft _ _

/-- The common level refines the finite level selected by the geometric
component classification. -/
noncomputable def classifiedOrbitCommonToComponent
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root
        (classifiedCoverAction diagram root source tempered))) :
    classifiedOrbitCommonLevel diagram root source tempered orbit ⟶
      (componentwiseTemperedClassification diagram root source tempered
        (classifiedCoverOrbitComponentEquiv
          diagram root source tempered orbit)).1 :=
  CategoryTheory.IsCofiltered.minToRight _ _

/-- The selected action-orbit presentation and the geometric component's
original finite presentation are isomorphic after pullback to the literal
inverse-limit group. -/
noncomputable def classifiedOrbitLimitIso
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root
        (classifiedCoverAction diagram root source tempered))) :
    literalOrbitLevelAction diagram root
        (classifiedCoverAction diagram root source tempered) orbit ≅
      (classifiedComponentLimitAction diagram root source tempered
        (classifiedCoverOrbitComponentEquiv
          diagram root source tempered orbit)).obj :=
  (literalOrbitLevelFactorization diagram root
    (classifiedCoverAction diagram root source tempered) orbit).comparison.trans
      (classifiedCoverOrbitLimitIso diagram root source tempered orbit)

/-! ## Comparison of the independently chosen finite presentations -/

/-- Regard an action of an unlifted finite deck group as an action of the
literal universe-lifted discrete coordinate group. -/
noncomputable def literalDeckAction
    (level : GaloisLevel diagram root)
    (object : SourceTemperoidAction (DeckGroup diagram root level)) :
    SourceTemperoidAction.{u, u + 1}
      ((literalTemperedPresentation diagram root).DiscreteLevel level) :=
  (ContAction.res SourceCountableTypeCat
    (deckULiftContinuousMulEquiv diagram root level)).obj
      object

/-- Pull an unlifted finite deck action all the way back to the literal
inverse-limit group. -/
noncomputable def literalDeckActionAtLimit
    (level : GaloisLevel diagram root)
    (object : SourceTemperoidAction (DeckGroup diagram root level)) :
    SourceTemperoidAction.{u, u + 1}
      (literalTemperedPresentation diagram root).Limit :=
  (ContAction.res SourceCountableTypeCat
    ((literalTemperedPresentation diagram root).continuousProjection level)).obj
      (literalDeckAction diagram root level object)

/-- Two finite deck actions whose pullbacks to the inverse limit are
isomorphic become isomorphic after restriction to any common refinement. -/
noncomputable def commonRefinementActionIso
    {first second common : GaloisLevel diagram root}
    (toFirst : common ⟶ first) (toSecond : common ⟶ second)
    (firstAction : SourceTemperoidAction (DeckGroup diagram root first))
    (secondAction : SourceTemperoidAction (DeckGroup diagram root second))
    (limitIso : literalDeckActionAtLimit diagram root first firstAction ≅
      literalDeckActionAtLimit diagram root second secondAction) :
    restrictDeckAction diagram root toFirst firstAction ≅
      restrictDeckAction diagram root toSecond secondAction := by
  let presentation := literalTemperedPresentation diagram root
  apply CategoryTheory.ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk limitIso.hom.hom.hom
        inv := SourceCountableTypeCat.homMk limitIso.inv.hom.hom
        hom_inv_id := by
          apply CategoryTheory.ConcreteCategory.hom_ext
          intro point
          exact congrArg
            (fun morphism : literalDeckActionAtLimit diagram root first
                  firstAction ⟶
                literalDeckActionAtLimit diagram root first firstAction ↦
              morphism.hom.hom point)
            limitIso.hom_inv_id
        inv_hom_id := by
          apply CategoryTheory.ConcreteCategory.hom_ext
          intro point
          exact congrArg
            (fun morphism : literalDeckActionAtLimit diagram root second
                  secondAction ⟶
                literalDeckActionAtLimit diagram root second secondAction ↦
              morphism.hom.hom point)
            limitIso.inv_hom_id }
  · intro transformation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro point
    obtain ⟨limitElement, atCommon⟩ :=
      literalTemperedPresentation_projection_surjective
        diagram root common (ULift.up transformation)
    have atFirst : presentation.projection first limitElement =
        ULift.up (deckTransition diagram root toFirst transformation) := by
      calc
        presentation.projection first limitElement =
            presentation.transition toFirst
              (presentation.projection common limitElement) :=
          (presentation.projection_transition toFirst limitElement).symm
        _ = presentation.transition toFirst (ULift.up transformation) :=
          congrArg (presentation.transition toFirst) atCommon
        _ = ULift.up
            (deckTransition diagram root toFirst transformation) := rfl
    have atSecond : presentation.projection second limitElement =
        ULift.up (deckTransition diagram root toSecond transformation) := by
      calc
        presentation.projection second limitElement =
            presentation.transition toSecond
              (presentation.projection common limitElement) :=
          (presentation.projection_transition toSecond limitElement).symm
        _ = presentation.transition toSecond (ULift.up transformation) :=
          congrArg (presentation.transition toSecond) atCommon
        _ = ULift.up
            (deckTransition diagram root toSecond transformation) := rfl
    have equivariant := CategoryTheory.ConcreteCategory.congr_hom
      (limitIso.hom.hom.comm limitElement) point
    change limitIso.hom.hom.hom
        (CategoryTheory.ConcreteCategory.hom
          ((literalDeckAction diagram root first firstAction).obj.ρ
            (presentation.projection first limitElement)) point) =
      CategoryTheory.ConcreteCategory.hom
        ((literalDeckAction diagram root second secondAction).obj.ρ
          (presentation.projection second limitElement))
        (limitIso.hom.hom.hom point) at equivariant
    rw [atFirst, atSecond] at equivariant
    exact equivariant

/-- At the common refinement, the finite action obtained from the arbitrary
orbit factorization is canonically isomorphic to the finite action originally
selected by geometric component classification. -/
noncomputable def classifiedOrbitCommonActionIso
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root
        (classifiedCoverAction diagram root source tempered))) :
    restrictDeckAction diagram root
        (classifiedOrbitCommonToAction diagram root source tempered orbit)
        (finiteDeckOrbitAction diagram root
          (classifiedCoverAction diagram root source tempered) orbit).obj ≅
      restrictDeckAction diagram root
        (classifiedOrbitCommonToComponent diagram root source tempered orbit)
        (classifiedComponentAction diagram root source tempered
          (classifiedCoverOrbitComponentEquiv
            diagram root source tempered orbit)).obj := by
  let factor := literalOrbitLevelFactorization diagram root
    (classifiedCoverAction diagram root source tempered) orbit
  let component := classifiedCoverOrbitComponentEquiv
    diagram root source tempered orbit
  let roundtripLevelIso :=
    (ContAction.res SourceCountableTypeCat
      ((literalTemperedPresentation diagram root).continuousProjection
        factor.level)).mapIso
      ((ContAction.resEquiv SourceCountableTypeCat
        (deckULiftContinuousMulEquiv diagram root factor.level)
        ).counitIso.app factor.levelAction)
  let limitIso : literalDeckActionAtLimit diagram root factor.level
        (finiteDeckOrbitAction diagram root
          (classifiedCoverAction diagram root source tempered) orbit).obj ≅
      literalDeckActionAtLimit diagram root
        (componentwiseTemperedClassification
          diagram root source tempered component).1
        (classifiedComponentAction diagram root source tempered component).obj := by
    exact roundtripLevelIso.trans
      (classifiedOrbitLimitIso diagram root source tempered orbit)
  exact commonRefinementActionIso diagram root
    (classifiedOrbitCommonToAction diagram root source tempered orbit)
    (classifiedOrbitCommonToComponent diagram root source tempered orbit)
    (finiteDeckOrbitAction diagram root
      (classifiedCoverAction diagram root source tempered) orbit).obj
    (classifiedComponentAction diagram root source tempered component).obj
    limitIso

/-- The geometric quotient produced from one reconstructed action orbit is
canonically the classified quotient of its original geometric component. -/
noncomputable def classifiedOrbitCoverIso
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root
        (classifiedCoverAction diagram root source tempered))) :
    finiteDeckOrbitCover diagram root
        (classifiedCoverAction diagram root source tempered) orbit ≅
      (associatedTemperedFunctor diagram root
        (componentwiseTemperedClassification diagram root source tempered
          (classifiedCoverOrbitComponentEquiv
            diagram root source tempered orbit)).1).obj
        (classifiedComponentAction diagram root source tempered
          (classifiedCoverOrbitComponentEquiv
            diagram root source tempered orbit)).obj :=
  (associatedTemperedRefinementIso diagram root
    (classifiedOrbitCommonToAction diagram root source tempered orbit)
    (finiteDeckOrbitAction diagram root
      (classifiedCoverAction diagram root source tempered) orbit).obj).symm.trans
    (((associatedTemperedFunctor diagram root
      (classifiedOrbitCommonLevel diagram root source tempered orbit)).mapIso
        (classifiedOrbitCommonActionIso diagram root source tempered orbit)).trans
      (associatedTemperedRefinementIso diagram root
        (classifiedOrbitCommonToComponent diagram root source tempered orbit)
        (classifiedComponentAction diagram root source tempered
          (classifiedCoverOrbitComponentEquiv
            diagram root source tempered orbit)).obj))

/-- The coproduct of orbit quotients of the reconstructed action is the
coproduct of the componentwise quotients selected from the geometric cover. -/
noncomputable def classifiedActionCoverComponentsIso
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source) :
    actionCoverCovObject diagram root
        (classifiedCoverAction diagram root source tempered) ≅
      SourceSemiGraphOfAnabelioids.CovObject.Coproduct.covObject
        (fun component : GeometricComponent source ↦
          classifiedComponentCover diagram root source tempered component) := by
  let orbitEquiv := classifiedCoverOrbitComponentEquiv
    diagram root source tempered
  let orbitIso := classifiedOrbitCoverIso diagram root source tempered
  let sourceFamily := fun orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root
        (classifiedCoverAction diagram root source tempered)) ↦
    (finiteDeckOrbitCover diagram root
      (classifiedCoverAction diagram root source tempered) orbit).obj
  let targetFamily := fun component : GeometricComponent source ↦
    classifiedComponentCover diagram root source tempered component
  let componentCoverIso : ∀ orbit,
      sourceFamily orbit ≅ targetFamily (orbitEquiv orbit) := fun orbit ↦
    (SourceSemiGraphOfAnabelioids.CovObject.temperedObjectProperty
      diagram root).ι.mapIso (orbitIso orbit)
  let componentMap : ∀ orbit,
      sourceFamily orbit ⟶ targetFamily (orbitEquiv orbit) := fun orbit ↦
    (componentCoverIso orbit).hom
  let coproductMap :=
    SourceSemiGraphOfAnabelioids.CovObject.Coproduct.map
      (source := sourceFamily) (target := targetFamily)
      orbitEquiv componentMap
  change SourceSemiGraphOfAnabelioids.CovObject.Coproduct.covObject
      sourceFamily ≅
    SourceSemiGraphOfAnabelioids.CovObject.Coproduct.covObject targetFamily
  apply covObjectIsoOfComponentwiseBijective coproductMap
  intro vertex
  let componentCarrierEquiv : ∀ orbit,
      ((finiteDeckOrbitCover diagram root
        (classifiedCoverAction diagram root source tempered) orbit
        ).obj.vertexObject vertex).obj.V.obj ≃
      ((classifiedComponentCover diagram root source tempered
        (orbitEquiv orbit)).vertexObject vertex).obj.V.obj := fun orbit ↦
    { toFun := (((componentCoverIso orbit).hom.app vertex).hom.hom)
      invFun := (((componentCoverIso orbit).inv.app vertex).hom.hom)
      left_inv := by
        intro point
        exact congrArg
          (fun morphism : sourceFamily orbit ⟶ sourceFamily orbit ↦
            (morphism.app vertex).hom.hom point)
          (componentCoverIso orbit).hom_inv_id
      right_inv := by
        intro point
        exact congrArg
          (fun morphism : targetFamily (orbitEquiv orbit) ⟶
              targetFamily (orbitEquiv orbit) ↦
            (morphism.app vertex).hom.hom point)
          (componentCoverIso orbit).inv_hom_id }
  let totalEquiv :
      (Σ orbit, ((sourceFamily orbit).vertexObject vertex).obj.V.obj) ≃
        (Σ component,
          ((targetFamily component).vertexObject vertex).obj.V.obj) :=
    Equiv.sigmaCongr orbitEquiv componentCarrierEquiv
  exact totalEquiv.bijective

/-- The reconstructed action cover is isomorphic to the original corrected
componentwise tempered cover. -/
noncomputable def classifiedActionCoverIso
    (target : SourceSemiGraphOfAnabelioids.CovObject.TemperedCover
      diagram root) :
    actionCoverObject diagram root
        (classifiedCoverAction diagram root target.obj target.property) ≅
      target := by
  apply CategoryTheory.ObjectProperty.isoMk
  exact
    (classifiedActionCoverComponentsIso
      diagram root target.obj target.property).trans
      (componentwiseAssociatedQuotientClassification
        diagram root target.obj target.property)

/-- Every corrected componentwise tempered geometric cover comes from an
action of the tempered deck group. -/
noncomputable instance actionCoverFunctorEssSurj :
    (actionCoverFunctor diagram root).EssSurj where
  mem_essImage target :=
    ⟨classifiedCoverAction diagram root target.obj target.property,
      ⟨classifiedActionCoverIso diagram root target⟩⟩

/-! ## The full action-cover equivalence -/

/-- The action-cover functor is an equivalence: it is faithful, full, and
essentially surjective. -/
noncomputable instance actionCoverFunctorIsEquivalence :
    (actionCoverFunctor diagram root).IsEquivalence where

/-- The full equivalence of *Semi-graphs of Anabelioids*, Proposition
3.6(ii), between countable continuous tempered-deck-group actions and the
literal geometric category of corrected tempered covers. -/
noncomputable def actionCoverEquivalence :
    SourceTemperoidAction.{u, u + 1} (TemperedDeckGroup diagram root) ≌
      SourceSemiGraphOfAnabelioids.CovObject.TemperedCover diagram root :=
  (actionCoverFunctor diagram root).asEquivalence

/-- The reverse functor supplied by the packaged action-cover equivalence. -/
noncomputable def coverActionFunctor :
    CategoryTheory.Functor
      (SourceSemiGraphOfAnabelioids.CovObject.TemperedCover diagram root)
      (SourceTemperoidAction.{u, u + 1}
        (TemperedDeckGroup diagram root)) :=
  (actionCoverEquivalence diagram root).inverse

/-- Unit of the action-cover equivalence. -/
noncomputable def actionCoverUnitIso :=
  (actionCoverEquivalence diagram root).unitIso

/-- Counit of the action-cover equivalence. -/
noncomputable def actionCoverCounitIso :=
  (actionCoverEquivalence diagram root).counitIso

/-- Naturality of the unit of the action-cover equivalence. -/
theorem actionCoverUnit_naturality
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)} (arrow : source ⟶ target) :
    CategoryTheory.CategoryStruct.comp
        ((actionCoverUnitIso diagram root).hom.app source)
        ((coverActionFunctor diagram root).map
          ((actionCoverFunctor diagram root).map arrow)) =
      CategoryTheory.CategoryStruct.comp arrow
        ((actionCoverUnitIso diagram root).hom.app target) :=
  (actionCoverEquivalence diagram root).unit_naturality arrow

/-- Naturality of the counit of the action-cover equivalence. -/
theorem actionCoverCounit_naturality
    {source target :
      SourceSemiGraphOfAnabelioids.CovObject.TemperedCover diagram root}
    (arrow : source ⟶ target) :
    CategoryTheory.CategoryStruct.comp
        ((actionCoverFunctor diagram root).map
          ((coverActionFunctor diagram root).map arrow))
        ((actionCoverCounitIso diagram root).hom.app target) =
      CategoryTheory.CategoryStruct.comp
        ((actionCoverCounitIso diagram root).hom.app source) arrow :=
  (actionCoverEquivalence diagram root).counit_naturality arrow

/-- Triangle identity on the action-to-cover functor. -/
theorem actionCoverFunctor_triangle
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)) :
    CategoryTheory.CategoryStruct.comp
        ((actionCoverFunctor diagram root).map
          ((actionCoverUnitIso diagram root).hom.app object))
        ((actionCoverCounitIso diagram root).hom.app
          ((actionCoverFunctor diagram root).obj object)) =
      CategoryTheory.CategoryStruct.id
        ((actionCoverFunctor diagram root).obj object) :=
  (actionCoverEquivalence diagram root).functor_unitIso_comp object

/-- Triangle identity on the reverse cover-to-action functor. -/
theorem coverActionFunctor_triangle
    (object : SourceSemiGraphOfAnabelioids.CovObject.TemperedCover
      diagram root) :
    CategoryTheory.CategoryStruct.comp
        ((actionCoverUnitIso diagram root).hom.app
          ((coverActionFunctor diagram root).obj object))
        ((coverActionFunctor diagram root).map
          ((actionCoverCounitIso diagram root).hom.app object)) =
      CategoryTheory.CategoryStruct.id
        ((coverActionFunctor diagram root).obj object) :=
  (actionCoverEquivalence diagram root).unit_inverse_comp object

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
