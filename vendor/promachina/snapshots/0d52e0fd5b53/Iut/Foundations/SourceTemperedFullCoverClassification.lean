/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedConnectedCoverClassification
import Iut.Foundations.SourceTemperedDeckProjectionSurjectivity

/-!
# Classifying globally bounded geometric covers at one Galois level

A globally splitting finite Galois level splits every vertex and edge
constituent, including all countably many geometric components. Varying the
initial target sheet therefore gives a map from that level's universal cover
onto every component.

This file extends the connected evaluation theorem accordingly.  The action
on all maps out of the universal cover need not be transitive; its orbits are
exactly the arbitrary countable component family. Following item (11) of the
May 2020 comments on *Semi-graphs of Anabelioids*, this is retained as the
globally bounded special case; corrected temperedness allows different
components to choose different levels.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

open SourceCombinatorialUniversalCover
open SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover
open SourceSemiGraphOfAnabelioids.GluedObject

/-- A path in the connected base lets a geometric target point be transported
back to some point above the root, without assuming that the whole target is
connected. -/
theorem exists_rootPoint_reachable
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex) (target : diagram.CovObject)
    (point : GeometricPoint target) :
    ∃ rootPoint : (target.vertexObject root).obj.V.obj,
      Relation.ReflTransGen (GeometricPointStep target)
        ⟨root, rootPoint⟩ point := by
  rcases point with ⟨vertex, point⟩
  rcases diagram.connected with connected | isolated
  · let path := connected.2.2 root vertex
    induction path with
    | refl => exact ⟨point, Relation.ReflTransGen.refl⟩
    | @tail middle final path adjacent inductionHypothesis =>
        rcases adjacent with
          ⟨edge, middleBranch, finalBranch, branchesDistinct,
            middleAbuts, finalAbuts⟩
        let first : diagram.IncidentBranch edge :=
          ⟨middleBranch, middle, middleAbuts⟩
        let second : diagram.IncidentBranch edge :=
          ⟨finalBranch, final, finalAbuts⟩
        let secondPoint :
            (second.temperoidPullback.obj
              (target.vertexObject second.vertex)).obj.V.obj := point
        let middlePoint :=
          (target.glue first second).inv.hom.hom secondPoint
        obtain ⟨rootPoint, rootPath⟩ := inductionHypothesis middlePoint
        refine ⟨rootPoint, rootPath.tail ?_⟩
        have step := GeometricPointStep.glue
          (source := target) first second middlePoint
        have mapsPoint :
            (target.glue first second).hom.hom.hom middlePoint =
              secondPoint := by
          exact (target.glue first second).inv_hom_id_apply secondPoint
        simpa only [middlePoint, mapsPoint, secondPoint] using step
  · letI : IsEmpty diagram.base.Vertex := isolated.1
    exact isEmptyElim root

/-- Image membership propagates along a geometric path.  This is the
pointwise form of constituent surjectivity and does not require the target's
other components to be connected to the chosen point. -/
theorem exists_preimage_of_reachable
    {diagram : SourceSemiGraphOfAnabelioids.{u}}
    {source target : diagram.CovObject} (map : source ⟶ target)
    (basePoint : GeometricPoint source) (targetPoint : GeometricPoint target)
    (reachable : Relation.ReflTransGen (GeometricPointStep target)
      (geometricPointMap map basePoint) targetPoint) :
    ∃ sourcePoint : GeometricPoint source,
      geometricPointMap map sourcePoint = targetPoint := by
  let InImage : GeometricPoint target → Prop := fun point ↦
    ∃ sourcePoint, geometricPointMap map sourcePoint = point
  have stepPreserves : ∀ {first second : GeometricPoint target},
      GeometricPointStep target first second →
        (InImage first → InImage second) := by
    intro first second step inImage
    rcases inImage with ⟨⟨sourceVertex, sourcePoint⟩, equality⟩
    cases step with
    | localAction targetVertex element targetPoint =>
        have vertexEquality : sourceVertex = targetVertex :=
          Sigma.mk.inj_iff.mp equality |>.1
        subst sourceVertex
        have pointEquality :
            (map.app targetVertex).hom.hom sourcePoint = targetPoint :=
          eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
        refine ⟨⟨targetVertex, element • sourcePoint⟩, ?_⟩
        apply Sigma.ext
        · rfl
        apply heq_of_eq
        exact (CategoryTheory.ConcreteCategory.congr_hom
          ((map.app targetVertex).hom.comm element) sourcePoint).trans
            (congrArg (element • ·) pointEquality)
    | @glue edge first second targetPoint =>
        have vertexEquality : sourceVertex = first.vertex :=
          Sigma.mk.inj_iff.mp equality |>.1
        subst sourceVertex
        have pointEquality :
            (map.app first.vertex).hom.hom sourcePoint = targetPoint :=
          eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
        refine ⟨⟨second.vertex,
          (source.glue first second).hom.hom.hom sourcePoint⟩, ?_⟩
        apply Sigma.ext
        · rfl
        apply heq_of_eq
        have naturality := CategoryTheory.ConcreteCategory.congr_hom
          (map.naturality first second) sourcePoint
        exact naturality.trans <|
          congrArg ((target.glue first second).hom.hom.hom) pointEquality
  have preserves : InImage (geometricPointMap map basePoint) →
      InImage targetPoint :=
    reachable.trans_induction_on
      (fun _ hypothesis ↦ hypothesis)
      (fun step ↦ stepPreserves step)
      (fun _ _ firstPreserves secondPreserves hypothesis ↦
        secondPreserves (firstPreserves hypothesis))
  exact preserves ⟨basePoint, rfl⟩

/-- At the root, varying the initial target sheet makes the geometric
domination map attain any prescribed target point. -/
theorem exists_geometricDomination_maps_root
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target)
    (targetPoint : (target.vertexObject root).obj.V.obj) :
    ∃ initial : (target.vertexObject root).obj.V.obj,
      ((GeometricDomination.hom diagram root level target split initial).app
        root).hom.hom (rootVertexPoint diagram root level) = targetPoint := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  letI := (diagram.vertexAnabelioid root).coverCategory
  let lifted : SourceSemiGraphUniversalCover.LiftedVertex
      (LevelSemiGraph diagram root level) level.rootVertex :=
    { path := UniversalVertex.base
        (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
      vertex := level.rootVertex
      endpoint_eq := rfl }
  let index : GeometricVertexIndex diagram root level root :=
    ⟨lifted, rfl⟩
  let component := SourceFiniteLevelUniversalCover.selectedVertexComponent
    diagram root level.object level.rootVertex root index
  let levelPoint :
      ((diagram.vertexAnabelioid root).finiteAction
        (level.object.vertexObject root)).obj.V.obj := level.point
  let canonical : SourceActionComponentFiber
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (level.object.vertexObject root)) component :=
    ⟨component.out, Quotient.out_eq' component⟩
  have sameComponent :
      (Quotient.mk'' levelPoint : SourceActionComponent
        (diagram.vertexAnabelioid root).group
        ((diagram.vertexAnabelioid root).finiteAction
          (level.object.vertexObject root))) = component := rfl
  have canonicalInOrbit : component.out ∈
      MulAction.orbit (diagram.vertexAnabelioid root).group levelPoint := by
    rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
    exact (Quotient.out_eq' component).trans sameComponent.symm
  obtain ⟨element, mapsCanonical⟩ :=
    MulAction.mem_orbit_iff.mp canonicalInOrbit
  let canonicalTarget := element • targetPoint
  let initial :=
    (TargetSheetLift.vertexTrivialization diagram root target root).symm
      canonicalTarget
  refine ⟨initial, ?_⟩
  have mapsBase :
      (GeometricDomination.vertexHom diagram root level target split initial
        root).hom.hom ⟨index, canonical⟩ = canonicalTarget := by
    rw [GeometricDomination.vertexHom_base]
    change TargetSheetLift.vertexTrivialization diagram root target root
        (SourceFiniteSheetSemiGraphCover.walkSheet
          (LevelSemiGraph diagram root level)
          (target.vertexObject root).obj.V.obj
          (TargetSheetLift.transport diagram root target level.object)
          (ReducedWalk.nil
            (graph := IncidenceGraph diagram root level)
            (root := IncidenceRoot diagram root level)) initial) =
      canonicalTarget
    rw [SourceFiniteSheetSemiGraphCover.walkSheet_nil]
    exact (TargetSheetLift.vertexTrivialization
      diagram root target root).apply_symm_apply canonicalTarget
  have actedRoot :
      element • rootVertexPoint diagram root level =
        (⟨index, canonical⟩ :
          (SourceFiniteLevelUniversalCover.covObject
            diagram root level.object level.rootVertex).vertexObject root
              |>.obj.V.obj) := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact mapsCanonical
  have equivariance := CategoryTheory.ConcreteCategory.congr_hom
    ((GeometricDomination.vertexHom diagram root level target split initial
      root).hom.comm element) (rootVertexPoint diagram root level)
  have mappedEquality : canonicalTarget = element •
      ((GeometricDomination.hom diagram root level target split initial).app
        root).hom.hom (rootVertexPoint diagram root level) := by
    calc
      canonicalTarget =
          (GeometricDomination.vertexHom diagram root level target split
            initial root).hom.hom ⟨index, canonical⟩ := mapsBase.symm
      _ = (GeometricDomination.vertexHom diagram root level target split
            initial root).hom.hom
          (element • rootVertexPoint diagram root level) := by rw [actedRoot]
      _ = element •
          (GeometricDomination.vertexHom diagram root level target split
            initial root).hom.hom (rootVertexPoint diagram root level) :=
        equivariance
  have cancelled := congrArg (element⁻¹ • ·) mappedEquality
  simpa [canonicalTarget, mul_smul] using cancelled.symm

/-- Every point of a cover split by one Galois level is hit by some map from
that level's geometric universal cover.  Different target components may use
different maps, but the source level is fixed globally. -/
theorem exists_universalMap_hitting
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target)
    (vertex : diagram.base.Vertex)
    (targetPoint : (target.vertexObject vertex).obj.V.obj) :
    ∃ map : SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex ⟶ target,
      ∃ sourcePoint, (map.app vertex).hom.hom sourcePoint = targetPoint := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  obtain ⟨rootPoint, targetPath⟩ :=
    exists_rootPoint_reachable diagram root target ⟨vertex, targetPoint⟩
  obtain ⟨initial, mapsRoot⟩ :=
    exists_geometricDomination_maps_root diagram root level target split
      rootPoint
  let map := GeometricDomination.hom
    diagram root level target split initial
  let sourceBase : GeometricPoint
      (SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex) :=
    ⟨root, rootVertexPoint diagram root level⟩
  have targetPath' :
      Relation.ReflTransGen (GeometricPointStep target)
        (geometricPointMap map sourceBase) ⟨vertex, targetPoint⟩ := by
    convert targetPath using 1
    apply Sigma.ext
    · rfl
    exact heq_of_eq mapsRoot
  obtain ⟨⟨sourceVertex, sourcePoint⟩, mapsPoint⟩ :=
    exists_preimage_of_reachable map sourceBase ⟨vertex, targetPoint⟩
      targetPath'
  have vertexEquality : sourceVertex = vertex :=
    Sigma.mk.inj_iff.mp mapsPoint |>.1
  subst sourceVertex
  exact ⟨map, sourcePoint,
    eq_of_heq (Sigma.mk.inj_iff.mp mapsPoint |>.2)⟩

/-- Evaluation from the associated quotient by the action on all universal
maps is surjective on every constituent.  Each target point may select its
own universal map, so no connectedness hypothesis on the whole target is
needed. -/
theorem homEvaluationMap_surjective_of_split
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target)
    (vertex : diagram.base.Vertex) :
    let source := SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex
    let deckAction := deckCovActionHom diagram root level
    let basePoint : GeometricPoint source :=
      ⟨root, rootVertexPoint diagram root level⟩
    let sourceConnected := covObject_isPointConnected diagram root level
    letI : Countable (source ⟶ target) :=
      homCountable basePoint sourceConnected
    letI : MulAction (DeckGroup diagram root level) (source ⟶ target) :=
      homDeckMulAction source target deckAction
    Function.Surjective
      ((homEvaluationMap source target deckAction basePoint sourceConnected).app
        vertex).hom.hom := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction := deckCovActionHom diagram root level
  let basePoint : GeometricPoint source :=
    ⟨root, rootVertexPoint diagram root level⟩
  let sourceConnected := covObject_isPointConnected diagram root level
  letI : Countable (source ⟶ target) :=
    homCountable basePoint sourceConnected
  letI : MulAction (DeckGroup diagram root level) (source ⟶ target) :=
    homDeckMulAction source target deckAction
  dsimp only
  intro targetPoint
  obtain ⟨map, sourcePoint, mapsPoint⟩ :=
    exists_universalMap_hitting diagram root level target split vertex
      targetPoint
  refine ⟨SourceTemperoidAssociatedQuotient.mk
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) (sourcePoint, map), ?_⟩
  exact (homEvaluationMap_mk source target deckAction basePoint
    sourceConnected vertex sourcePoint map).trans mapsPoint

/-- Evaluation is componentwise bijective for an arbitrary cover split by
the chosen level. -/
theorem homEvaluationMap_bijective_of_split
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target)
    (vertex : diagram.base.Vertex) :
    let source := SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex
    let deckAction := deckCovActionHom diagram root level
    let basePoint : GeometricPoint source :=
      ⟨root, rootVertexPoint diagram root level⟩
    let sourceConnected := covObject_isPointConnected diagram root level
    letI : Countable (source ⟶ target) :=
      homCountable basePoint sourceConnected
    letI : MulAction (DeckGroup diagram root level) (source ⟶ target) :=
      homDeckMulAction source target deckAction
    Function.Bijective
      ((homEvaluationMap source target deckAction basePoint sourceConnected).app
        vertex).hom.hom := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction := deckCovActionHom diagram root level
  let basePoint : GeometricPoint source :=
    ⟨root, rootVertexPoint diagram root level⟩
  let sourceConnected := covObject_isPointConnected diagram root level
  letI : Countable (source ⟶ target) :=
    homCountable basePoint sourceConnected
  letI : MulAction (DeckGroup diagram root level) (source ⟶ target) :=
    homDeckMulAction source target deckAction
  dsimp only
  exact ⟨homEvaluationMap_injective source target deckAction basePoint
      sourceConnected vertex
      (vertexDeckAction_isPretransitive diagram root level vertex),
    homEvaluationMap_surjective_of_split
      diagram root level target split vertex⟩

/-- The action on all maps out of one splitting universal level reconstructs
the entire geometric cover, with all of its countable components. -/
noncomputable def homEvaluationIsoOfSplit
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target) :
    let source := SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex
    let deckAction := deckCovActionHom diagram root level
    let basePoint : GeometricPoint source :=
      ⟨root, rootVertexPoint diagram root level⟩
    let sourceConnected := covObject_isPointConnected diagram root level
    letI : Countable (source ⟶ target) :=
      homCountable basePoint sourceConnected
    letI : MulAction (DeckGroup diagram root level) (source ⟶ target) :=
      homDeckMulAction source target deckAction
    covObject source deckAction (source ⟶ target) ≅ target := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction := deckCovActionHom diagram root level
  let basePoint : GeometricPoint source :=
    ⟨root, rootVertexPoint diagram root level⟩
  let sourceConnected := covObject_isPointConnected diagram root level
  letI : Countable (source ⟶ target) :=
    homCountable basePoint sourceConnected
  letI : MulAction (DeckGroup diagram root level) (source ⟶ target) :=
    homDeckMulAction source target deckAction
  dsimp only
  exact covObjectIsoOfComponentwiseBijective
    (homEvaluationMap source target deckAction basePoint sourceConnected)
    (homEvaluationMap_bijective_of_split
      diagram root level target split)

/-- The possibly disconnected finite-level deck action recovered from a
geometric cover split by that level. -/
noncomputable def finiteLevelFullAction
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (target : diagram.CovObject) :
    SourceTemperoidAction (DeckGroup diagram root level) := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  exact homAction source target (deckCovActionHom diagram root level)
    ⟨root, rootVertexPoint diagram root level⟩
    (covObject_isPointConnected diagram root level)

/-- The full finite-level action comparison, without a connectedness
restriction. -/
noncomputable def finiteLevelFullComparison
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target) :
    (((associatedTemperedFunctor diagram root level).obj
      (finiteLevelFullAction diagram root level target)).obj) ≅ target :=
  homEvaluationIsoOfSplit diagram root level target split

/-- Every globally bounded geometric cover is an associated quotient at one
globally splitting Galois level. -/
noncomputable def globallyTemperedClassification
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (target : diagram.CovObject)
    (tempered : IsGloballyTempered diagram root target) :
    Σ level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
        diagram root,
      Σ action : SourceTemperoidAction (DeckGroup diagram root level),
        (((associatedTemperedFunctor diagram root level).obj action).obj ≅
          target) := by
  let splitting := exists_galoisLevel_splitting diagram root tempered
  let level := Classical.choose splitting
  let split := Classical.choose_spec splitting
  exact ⟨level, finiteLevelFullAction diagram root level target,
    finiteLevelFullComparison diagram root level target split⟩

end SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

end Iut
