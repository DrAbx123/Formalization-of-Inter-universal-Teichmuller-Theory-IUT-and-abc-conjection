/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedAssociatedCoverQuotient

/-!
# Classifying connected geometric subcovers

For a point-connected geometric universal cover `U` with deck group `Deck`
and a geometric subcover `H`, the maps `U ⟶ H` carry the inverse-
precomposition deck action.  Evaluation descends to a geometric morphism

`(U × Hom(U, H)) / Deck ⟶ H`.

This is the concrete replacement for the fiber-product component argument in
the proof of *Semi-graphs of Anabelioids*, Proposition 3.6(ii).  No geometric
cover is defined through the action category: the auxiliary action is
recovered from the already constructed literal cover and its morphisms.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

open SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

variable {Deck : Type u} [Group Deck]
variable {diagram : SourceSemiGraphOfAnabelioids.{u}}

/-- A constituentwise bijective geometric-cover morphism is an isomorphism.
The inverse is constructed on the concrete constituent carriers; its local
equivariance and gluing naturality follow by cancellation against the given
bijective maps. -/
noncomputable def covObjectIsoOfComponentwiseBijective
    {source target : diagram.CovObject} (map : source ⟶ target)
    (bijective : ∀ vertex,
      Function.Bijective (map.app vertex).hom.hom) :
    source ≅ target := by
  let carrierEquiv (vertex : diagram.base.Vertex) :
      (source.vertexObject vertex).obj.V.obj ≃
        (target.vertexObject vertex).obj.V.obj :=
    Equiv.ofBijective (map.app vertex).hom.hom (bijective vertex)
  let inverseVertex (vertex : diagram.base.Vertex) :
      target.vertexObject vertex ⟶ source.vertexObject vertex := by
    apply ObjectProperty.homMk
    refine
      { hom := SourceCountableTypeCat.homMk (carrierEquiv vertex).symm
        comm := ?_ }
    intro element
    apply ConcreteCategory.hom_ext
    intro point
    apply (carrierEquiv vertex).injective
    calc
      carrierEquiv vertex ((carrierEquiv vertex).symm (element • point)) =
          element • point := (carrierEquiv vertex).apply_symm_apply _
      _ = element • carrierEquiv vertex ((carrierEquiv vertex).symm point) :=
        congrArg (element • ·) ((carrierEquiv vertex).apply_symm_apply point).symm
      _ = carrierEquiv vertex (element • (carrierEquiv vertex).symm point) :=
        (ConcreteCategory.congr_hom
          ((map.app vertex).hom.comm element)
          ((carrierEquiv vertex).symm point)).symm
  let inverse : target ⟶ source :=
    { app := inverseVertex
      naturality := by
        intro edge left right
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext
        intro point
        apply (carrierEquiv right.vertex).injective
        have naturality :=
          ConcreteCategory.congr_hom (map.naturality left right)
            ((carrierEquiv left.vertex).symm point)
        change carrierEquiv right.vertex
              (ConcreteCategory.hom (source.glue left right).hom.hom
                ((carrierEquiv left.vertex).symm point)) =
            ConcreteCategory.hom (target.glue left right).hom.hom
              (carrierEquiv left.vertex
                ((carrierEquiv left.vertex).symm point))
          at naturality
        have rightCancellation :=
          (carrierEquiv right.vertex).apply_symm_apply
            (ConcreteCategory.hom (target.glue left right).hom.hom point)
        have leftCancellation := congrArg
          (ConcreteCategory.hom (target.glue left right).hom.hom)
          ((carrierEquiv left.vertex).apply_symm_apply point).symm
        exact rightCancellation.trans
          (leftCancellation.trans naturality.symm) }
  exact
    { hom := map
      inv := inverse
      hom_inv_id := by
        apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
        intro vertex
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext
        intro point
        exact (carrierEquiv vertex).symm_apply_apply point
      inv_hom_id := by
        apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
        intro vertex
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext
        intro point
        exact (carrierEquiv vertex).apply_symm_apply point }

/-- The countable continuous deck action on maps from a point-connected
source, for a discrete finite-level deck group. -/
noncomputable def homAction
    [TopologicalSpace Deck] [IsTopologicalGroup Deck] [DiscreteTopology Deck]
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint) :
    SourceTemperoidAction Deck := by
  letI : Countable (source ⟶ target) := homCountable basePoint connected
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  let action : Action SourceCountableTypeCat.{u} Deck :=
    SourceCountableTypeCat.ofMulAction Deck
      (SourceCountableTypeCat.of (source ⟶ target))
  refine ⟨action, ?_⟩
  change ContinuousSMul Deck
    ((forget₂ (Action SourceCountableTypeCat.{u} Deck) TopCat).obj action)
  letI : DiscreteTopology
      ((forget₂ (Action SourceCountableTypeCat.{u} Deck) TopCat).obj action) :=
    ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro map
  exact isOpen_discrete _

/-- Evaluation of a represented source-point/map pair. -/
noncomputable def homFiberEvaluation
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (vertex : diagram.base.Vertex) :
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    SourceTemperoidAssociatedQuotient.Carrier
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex) (source ⟶ target) →
      (target.vertexObject vertex).obj.V.obj := by
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) (source ⟶ target)
  intro quotientPoint
  exact Quotient.liftOn' quotientPoint
    (fun point ↦ ConcreteCategory.hom
      (point.2.app vertex).hom.hom point.1) (by
      intro first second related
      rw [MulAction.orbitRel_apply] at related
      obtain ⟨transformation, equality⟩ :=
        MulAction.mem_orbit_iff.mp related
      rw [← equality]
      change ConcreteCategory.hom
          (((deckAction transformation).inv ≫ second.2).app vertex).hom.hom
          ((vertexDeckAction source deckAction vertex transformation).hom.hom.hom
            second.1) =
        ConcreteCategory.hom (second.2.app vertex).hom.hom second.1
      change ConcreteCategory.hom (second.2.app vertex).hom.hom
          (ConcreteCategory.hom
            ((deckAction transformation).inv.app vertex).hom.hom
              (ConcreteCategory.hom
                ((deckAction transformation).hom.app vertex).hom.hom
                second.1)) =
        ConcreteCategory.hom (second.2.app vertex).hom.hom second.1
      have cancellation := congrArg
        (fun morphism : source ⟶ source ↦
          ConcreteCategory.hom (morphism.app vertex).hom.hom second.1)
        (deckAction transformation).hom_inv_id
      exact congrArg
        (ConcreteCategory.hom (second.2.app vertex).hom.hom) cancellation)

@[simp]
theorem homFiberEvaluation_mk
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (vertex : diagram.base.Vertex)
    (point : (source.vertexObject vertex).obj.V.obj × (source ⟶ target)) :
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    homFiberEvaluation source target deckAction vertex
        (SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject vertex)
          (vertexDeckAction source deckAction vertex) point) =
      ConcreteCategory.hom (point.2.app vertex).hom.hom point.1 :=
  rfl

/-- Evaluation is locally equivariant and therefore defines a morphism from
the associated quotient constituent to the target constituent. -/
noncomputable def homVertexEvaluation
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint)
    (vertex : diagram.base.Vertex) :
    letI : Countable (source ⟶ target) := homCountable basePoint connected
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    vertexAction source deckAction (source ⟶ target) vertex ⟶
      target.vertexObject vertex := by
  letI : Countable (source ⟶ target) := homCountable basePoint connected
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  apply ObjectProperty.homMk
  refine
    { hom := SourceCountableTypeCat.homMk
        (homFiberEvaluation source target deckAction vertex)
      comm := ?_ }
  intro element
  apply ConcreteCategory.hom_ext
  intro quotientPoint
  letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) (source ⟶ target)
  induction quotientPoint using Quotient.inductionOn' with
  | _ point =>
      exact ConcreteCategory.congr_hom
        ((point.2.app vertex).hom.comm element) point.1

/-- The constituent evaluation maps commute with every branch gluing and
assemble into a literal geometric-cover morphism. -/
noncomputable def homEvaluationMap
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint) :
    letI : Countable (source ⟶ target) := homCountable basePoint connected
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    covObject source deckAction (source ⟶ target) ⟶ target := by
  letI : Countable (source ⟶ target) := homCountable basePoint connected
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  refine
    { app := homVertexEvaluation source target deckAction basePoint connected
      naturality := ?_ }
  intro edge left right
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro quotientPoint
  letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
    (source.vertexObject left.vertex)
    (vertexDeckAction source deckAction left.vertex) (source ⟶ target)
  induction quotientPoint using Quotient.inductionOn' with
  | _ point =>
      have naturality := ConcreteCategory.congr_hom
        (point.2.naturality left right) point.1
      change ConcreteCategory.hom (point.2.app right.vertex).hom.hom
            (ConcreteCategory.hom (source.glue left right).hom.hom point.1) =
          ConcreteCategory.hom (target.glue left right).hom.hom
            (ConcreteCategory.hom (point.2.app left.vertex).hom.hom point.1)
        at naturality
      exact naturality

@[simp]
theorem homEvaluationMap_mk
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint)
    (vertex : diagram.base.Vertex)
    (sourcePoint : (source.vertexObject vertex).obj.V.obj)
    (map : source ⟶ target) :
    letI : Countable (source ⟶ target) := homCountable basePoint connected
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    ((homEvaluationMap source target deckAction basePoint connected).app
      vertex).hom.hom
        (SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject vertex)
          (vertexDeckAction source deckAction vertex) (sourcePoint, map)) =
      ConcreteCategory.hom (map.app vertex).hom.hom sourcePoint := by
  letI : Countable (source ⟶ target) := homCountable basePoint connected
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  change homFiberEvaluation source target deckAction vertex
      (SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex) (sourcePoint, map)) =
    ConcreteCategory.hom (map.app vertex).hom.hom sourcePoint
  exact homFiberEvaluation_mk source target deckAction vertex
    (sourcePoint, map)

/-- Every constituent evaluation is surjective as soon as one displayed map
from the source lands in the connected target. -/
theorem homEvaluationMap_surjective
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (sourceConnected : IsPointConnected source basePoint)
    (baseMap : source ⟶ target)
    (targetConnected : IsPointConnected target
      (geometricPointMap baseMap basePoint))
    (vertex : diagram.base.Vertex) :
    letI : Countable (source ⟶ target) :=
      homCountable basePoint sourceConnected
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    Function.Surjective
      ((homEvaluationMap source target deckAction basePoint sourceConnected).app
        vertex).hom.hom := by
  letI : Countable (source ⟶ target) :=
    homCountable basePoint sourceConnected
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  intro targetPoint
  obtain ⟨sourcePoint, equality⟩ :=
    hom_surjective_of_target_isPointConnected
      baseMap basePoint targetConnected vertex targetPoint
  refine ⟨SourceTemperoidAssociatedQuotient.mk
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) (sourcePoint, baseMap), ?_⟩
  exact (homEvaluationMap_mk source target deckAction basePoint
    sourceConnected vertex sourcePoint baseMap).trans equality

/-- Under transitivity of the source deck action at the chosen vertex,
evaluation is injective on that constituent.  Equal evaluations let one deck
transformation align the two source points; point-connectedness then forces
the two maps to agree globally. -/
theorem homEvaluationMap_injective
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (sourceConnected : IsPointConnected source basePoint)
    (vertex : diagram.base.Vertex)
    (deckTransitive :
      letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex)
      MulAction.IsPretransitive Deck
        (source.vertexObject vertex).obj.V.obj) :
    letI : Countable (source ⟶ target) :=
      homCountable basePoint sourceConnected
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    Function.Injective
      ((homEvaluationMap source target deckAction basePoint sourceConnected).app
        vertex).hom.hom := by
  letI : Countable (source ⟶ target) :=
    homCountable basePoint sourceConnected
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex)
  intro firstQuotient secondQuotient evaluationEquality
  letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) (source ⟶ target)
  induction firstQuotient using Quotient.inductionOn' with
  | _ first =>
      induction secondQuotient using Quotient.inductionOn' with
      | _ second =>
          change ConcreteCategory.hom (first.2.app vertex).hom.hom first.1 =
            ConcreteCategory.hom (second.2.app vertex).hom.hom second.1
            at evaluationEquality
          obtain ⟨transformation, sourceEquality⟩ :=
            deckTransitive.exists_smul_eq first.1 second.1
          change (vertexDeckAction source deckAction vertex transformation).hom.hom.hom
              first.1 = second.1 at sourceEquality
          have inverseSourceEquality :
              ConcreteCategory.hom
                  (vertexDeckAction source deckAction vertex transformation).inv.hom.hom
                  second.1 = first.1 := by
            have applied := congrArg
              (ConcreteCategory.hom
                (vertexDeckAction source deckAction vertex transformation).inv.hom.hom)
              sourceEquality
            have cancellation :=
              (vertexDeckAction source deckAction vertex transformation)
                |>.hom_inv_id_apply first.1
            exact applied.symm.trans cancellation
          have mapEquality : transformation • first.2 = second.2 := by
            apply hom_ext_of_isPointConnected
              (⟨vertex, second.1⟩ : GeometricPoint source)
              (sourceConnected.rebase ⟨vertex, second.1⟩)
            change ConcreteCategory.hom (first.2.app vertex).hom.hom
                (ConcreteCategory.hom
                  (vertexDeckAction source deckAction vertex transformation).inv.hom.hom
                  second.1) =
              ConcreteCategory.hom (second.2.app vertex).hom.hom second.1
            rw [inverseSourceEquality]
            exact evaluationEquality
          have orbitEquality :=
            SourceTemperoidAssociatedQuotient.mk_smul
              (source.vertexObject vertex)
              (vertexDeckAction source deckAction vertex)
              transformation first
          rw [sourceEquality, mapEquality] at orbitEquality
          exact orbitEquality.symm

/-- The evaluation morphism is constituentwise bijective under the universal
deck-transitivity and connected-target hypotheses. -/
theorem homEvaluationMap_bijective
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (sourceConnected : IsPointConnected source basePoint)
    (baseMap : source ⟶ target)
    (targetConnected : IsPointConnected target
      (geometricPointMap baseMap basePoint))
    (deckTransitive : ∀ vertex,
      letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex)
      MulAction.IsPretransitive Deck
        (source.vertexObject vertex).obj.V.obj)
    (vertex : diagram.base.Vertex) :
    letI : Countable (source ⟶ target) :=
      homCountable basePoint sourceConnected
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    Function.Bijective
      ((homEvaluationMap source target deckAction basePoint sourceConnected).app
        vertex).hom.hom :=
  ⟨homEvaluationMap_injective source target deckAction basePoint
      sourceConnected vertex (deckTransitive vertex),
    homEvaluationMap_surjective source target deckAction basePoint
      sourceConnected baseMap targetConnected vertex⟩

/-- Maps from the universal source to a connected subcover form a transitive
deck set.  Surjectivity of one map selects a source point over the desired
target value, and root deck transitivity moves the chosen base point there. -/
theorem homDeckMulAction_isPretransitive
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (sourceConnected : IsPointConnected source basePoint)
    (baseMap : source ⟶ target)
    (targetConnected : IsPointConnected target
      (geometricPointMap baseMap basePoint))
    (deckTransitive :
      letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
        (source.vertexObject basePoint.1)
        (vertexDeckAction source deckAction basePoint.1)
      MulAction.IsPretransitive Deck
        (source.vertexObject basePoint.1).obj.V.obj) :
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    MulAction.IsPretransitive Deck (source ⟶ target) := by
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
    (source.vertexObject basePoint.1)
    (vertexDeckAction source deckAction basePoint.1)
  constructor
  intro first second
  have firstTargetConnected := targetConnected.rebase
    (geometricPointMap first basePoint)
  obtain ⟨sourcePoint, evaluationEquality⟩ :=
    hom_surjective_of_target_isPointConnected
      first basePoint firstTargetConnected basePoint.1
        (ConcreteCategory.hom
          (second.app basePoint.1).hom.hom basePoint.2)
  obtain ⟨transformation, sourceEquality⟩ :=
    deckTransitive.exists_smul_eq basePoint.2 sourcePoint
  change (vertexDeckAction source deckAction basePoint.1 transformation).hom.hom.hom
      basePoint.2 = sourcePoint at sourceEquality
  refine ⟨transformation⁻¹, ?_⟩
  apply hom_ext_of_isPointConnected basePoint sourceConnected
  change ConcreteCategory.hom (first.app basePoint.1).hom.hom
      (ConcreteCategory.hom
        ((deckAction transformation⁻¹).inv.app basePoint.1).hom.hom
        basePoint.2) =
    ConcreteCategory.hom (second.app basePoint.1).hom.hom basePoint.2
  rw [map_inv]
  change ConcreteCategory.hom (first.app basePoint.1).hom.hom
      ((vertexDeckAction source deckAction basePoint.1 transformation).hom.hom.hom
        basePoint.2) =
    ConcreteCategory.hom (second.app basePoint.1).hom.hom basePoint.2
  rw [sourceEquality]
  exact evaluationEquality

/-- The recovered map action is a connected object of the finite-level
temperoid. -/
theorem homAction_isConnected
    [TopologicalSpace Deck] [IsTopologicalGroup Deck] [DiscreteTopology Deck]
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (sourceConnected : IsPointConnected source basePoint)
    (baseMap : source ⟶ target)
    (targetConnected : IsPointConnected target
      (geometricPointMap baseMap basePoint))
    (deckTransitive :
      letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
        (source.vertexObject basePoint.1)
        (vertexDeckAction source deckAction basePoint.1)
      MulAction.IsPretransitive Deck
        (source.vertexObject basePoint.1).obj.V.obj) :
    sourceConnectedTemperoidAction Deck
      (homAction source target deckAction basePoint sourceConnected) := by
  letI : Countable (source ⟶ target) :=
    homCountable basePoint sourceConnected
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  constructor
  · exact ⟨baseMap⟩
  · exact homDeckMulAction_isPretransitive source target deckAction
      basePoint sourceConnected baseMap targetConnected deckTransitive

/-- Evaluation identifies a connected geometric subcover with the associated
quotient built from the recovered transitive deck action on source maps. -/
noncomputable def homEvaluationIso
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source)
    (basePoint : GeometricPoint source)
    (sourceConnected : IsPointConnected source basePoint)
    (baseMap : source ⟶ target)
    (targetConnected : IsPointConnected target
      (geometricPointMap baseMap basePoint))
    (deckTransitive : ∀ vertex,
      letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex)
      MulAction.IsPretransitive Deck
        (source.vertexObject vertex).obj.V.obj) :
    letI : Countable (source ⟶ target) :=
      homCountable basePoint sourceConnected
    letI : MulAction Deck (source ⟶ target) :=
      homDeckMulAction source target deckAction
    covObject source deckAction (source ⟶ target) ≅ target := by
  letI : Countable (source ⟶ target) :=
    homCountable basePoint sourceConnected
  letI : MulAction Deck (source ⟶ target) :=
    homDeckMulAction source target deckAction
  exact covObjectIsoOfComponentwiseBijective
    (homEvaluationMap source target deckAction basePoint sourceConnected)
    (homEvaluationMap_bijective source target deckAction basePoint
      sourceConnected baseMap targetConnected deckTransitive)

/-! ## Finite Galois-level classification -/

/-- The connected deck action recovered from maps out of a concrete
finite-level geometric universal cover. -/
noncomputable def finiteLevelSubcoverAction
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (target : diagram.CovObject)
    (map : SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex ⟶ target)
    (targetConnected : IsPointConnected target
      (geometricPointMap map
        ⟨root, rootVertexPoint diagram root level⟩)) :
    SourceConnectedTemperoid (DeckGroup diagram root level) := by
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let basePoint : GeometricPoint source :=
    ⟨root, rootVertexPoint diagram root level⟩
  let sourceConnected := covObject_isPointConnected diagram root level
  let geometricDeckAction := deckCovActionHom diagram root level
  let recovered := homAction source target geometricDeckAction
    basePoint sourceConnected
  refine ⟨recovered, ?_⟩
  exact homAction_isConnected source target geometricDeckAction
    basePoint sourceConnected map targetConnected
      (rootVertexDeckAction_isPretransitive diagram root level)

/-- Evaluation identifies the associated quotient of the recovered map
action with the original connected finite-level subcover. -/
noncomputable def finiteLevelSubcoverComparison
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (target : diagram.CovObject)
    (map : SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex ⟶ target)
    (targetConnected : IsPointConnected target
      (geometricPointMap map
        ⟨root, rootVertexPoint diagram root level⟩)) :
    (((associatedTemperedFunctor diagram root level).obj
      (finiteLevelSubcoverAction diagram root level target map
        targetConnected).obj).obj) ≅ target := by
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let basePoint : GeometricPoint source :=
    ⟨root, rootVertexPoint diagram root level⟩
  let sourceConnected := covObject_isPointConnected diagram root level
  let geometricDeckAction := deckCovActionHom diagram root level
  exact homEvaluationIso source target geometricDeckAction basePoint
    sourceConnected map targetConnected
      (fun vertex ↦
        vertexDeckAction_isPretransitive diagram root level vertex)

/-- Every intrinsically connected geometric subcover of a finite-level
universal cover is an associated quotient by a recovered transitive deck
action.  This is the object-classification conclusion of Proposition 3.6(ii)
at one Galois level. -/
noncomputable def finiteLevelClassificationOfSubcover
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (target : diagram.CovObject)
    (subcover : SourceSemiGraphOfAnabelioids.CovObject.IsSubcoverOf target
      (SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex))
    (connected : IsGeometricallyConnected target) :
    Σ action : SourceConnectedTemperoid (DeckGroup diagram root level),
      (((associatedTemperedFunctor diagram root level).obj action.obj).obj ≅
        target) := by
  let map := Classical.choice subcover
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let basePoint : GeometricPoint source :=
    ⟨root, rootVertexPoint diagram root level⟩
  let targetConnected : IsPointConnected target
      (geometricPointMap map basePoint) :=
    (Classical.choose_spec connected).rebase (geometricPointMap map basePoint)
  exact ⟨finiteLevelSubcoverAction diagram root level target map
      targetConnected,
    finiteLevelSubcoverComparison diagram root level target map
      targetConnected⟩

end SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

end Iut
