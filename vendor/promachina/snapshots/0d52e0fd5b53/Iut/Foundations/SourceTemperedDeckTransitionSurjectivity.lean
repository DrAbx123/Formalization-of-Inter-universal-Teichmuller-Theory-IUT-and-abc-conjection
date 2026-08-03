/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceCombinatorialUniversalCover

/-!
# Surjectivity of tempered deck transitions

The finite Galois refinements used to define the tempered fundamental group
must induce surjections on their complete combinatorial deck groups.  The
missing ingredient is local, rather than merely pointwise, surjectivity of
the incidence refinement: reduced walks have to lift one adjacent node at a
time from a prescribed starting lift.

This file isolates that path-lifting argument.  It first proves the generic
universal-tree statement, then verifies local lifting for the finite-etale
incidence projections and their Galois refinements.
-/

namespace Iut

universe u

open CategoryTheory

namespace SourceCombinatorialUniversalCover

namespace UniversalVertex

variable {Vertex Target : Type u}
    (graph : SimpleGraph Vertex) (root : Vertex)

/-- A graph homomorphism is locally surjective when every neighbor of the
image of a selected source vertex has a neighboring lift at that vertex. -/
def IsLocallySurjective (targetGraph : SimpleGraph Target)
    (hom : graph →g targetGraph) : Prop :=
  ∀ {center : Vertex} {target : Target},
    targetGraph.Adj (hom center) target →
      ∃ source : Vertex, graph.Adj center source ∧ hom source = target

/-- A locally surjective graph homomorphism induces a surjection between the
reduced-walk universal trees. -/
theorem mapHom_surjective_of_locallySurjective
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallySurjective : IsLocallySurjective graph targetGraph hom) :
    Function.Surjective (mapHom graph root targetGraph hom) := by
  intro target
  obtain ⟨walk⟩ :=
    (tree_connected targetGraph (hom root))
      (base targetGraph (hom root)) target
  have liftAlong : ∀ {source destination}
      (path : (tree targetGraph (hom root)).Walk source destination)
      (preimage : UniversalVertex graph root),
      mapHom graph root targetGraph hom preimage = source →
        ∃ result, mapHom graph root targetGraph hom result = destination := by
    intro source destination path
    induction path with
    | nil =>
        intro preimage equality
        exact ⟨preimage, equality⟩
    | @cons source neighbor destination adjacent tail inductionHypothesis =>
        intro preimage equality
        have endpointAdjacent :
            targetGraph.Adj (hom preimage.endpoint) neighbor.endpoint := by
          rw [← mapHom_endpoint graph root targetGraph hom preimage, equality]
          exact endpoint_adj targetGraph (hom root) adjacent
        obtain ⟨nextEndpoint, nextEndpointAdjacent, mappedEndpoint⟩ :=
          locallySurjective endpointAdjacent
        let next : UniversalVertex graph root :=
          liftNeighbor graph root preimage nextEndpoint nextEndpointAdjacent
        have nextAdjacent :
            (tree graph root).Adj preimage next :=
          adjacent_liftNeighbor graph root _ _ _
        have mappedNextAdjacent :
            (tree targetGraph (hom root)).Adj source
              (mapHom graph root targetGraph hom next) := by
          rw [← equality]
          exact mapHom_adj graph root targetGraph hom nextAdjacent
        have mappedNextEndpoint :
            (mapHom graph root targetGraph hom next).endpoint =
              neighbor.endpoint := by
          rw [mapHom_endpoint, liftNeighbor_endpoint, mappedEndpoint]
        have mappedNext :
            mapHom graph root targetGraph hom next = neighbor :=
          neighbor_eq_of_endpoint_eq targetGraph (hom root)
            mappedNextAdjacent adjacent mappedNextEndpoint
        exact inductionHypothesis next mappedNext
  exact liftAlong walk (base graph root) (mapHom_base graph root targetGraph hom)

/-- Changing only the equality witness for a universal-tree root is
surjective. -/
theorem castRoot_surjective {first second : Vertex} (rootsEqual : first = second) :
    Function.Surjective (castRoot graph rootsEqual) := by
  subst second
  exact Function.surjective_id

end UniversalVertex

namespace SourceGaloisCombinatorialUniversalCover

open SourceSemiGraphOfAnabelioids.GluedObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)

/-- Two points of a finer Galois object with the same image differ by an
automorphism in the kernel of automorphism descent. -/
theorem exists_kernelAutomorphism_of_fiber_eq
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) (vertex : diagram.base.Vertex)
    (first second : (rootFiber diagram vertex).obj finer.object)
    (sameImage : (rootFiber diagram vertex).map refinement.val first =
      (rootFiber diagram vertex).map refinement.val second) :
    ∃ automorphism : Aut finer.object,
      (rootFiber diagram vertex).map automorphism.hom first = second ∧
        GaloisLevel.automorphismTransition diagram root refinement
          automorphism = 1 := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram vertex) :=
    rootFiberFunctor diagram vertex
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  obtain ⟨automorphism, pointEquality⟩ :=
    MulAction.exists_smul_eq (Aut finer.object) first second
  change (rootFiber diagram vertex).map automorphism.hom first = second at pointEquality
  refine ⟨automorphism, pointEquality, ?_⟩
  change PreGaloisCategory.autMap refinement.val automorphism = 1
  apply PreGaloisCategory.evaluation_aut_injective_of_isConnected
    (rootFiber diagram vertex) coarser.object
      ((rootFiber diagram vertex).map refinement.val first)
  change (rootFiber diagram vertex).map
      (PreGaloisCategory.autMap refinement.val automorphism).hom
        ((rootFiber diagram vertex).map refinement.val first) =
    (rootFiber diagram vertex).map (1 : Aut coarser.object).hom
      ((rootFiber diagram vertex).map refinement.val first)
  rw [PreGaloisCategory.comp_autMap_apply, pointEquality, sameImage]
  exact (Functor.map_id_apply (rootFiber diagram vertex) coarser.object _).symm

/-- The kernel of automorphism descent is transitive on every fiber of the
vertex-component transition map. -/
theorem transitionVertex_kernel_transitive
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (first second : finer.semiGraph.Vertex)
    (sameImage : (GaloisLevel.transition diagram root refinement).vertexMap
        first =
      (GaloisLevel.transition diagram root refinement).vertexMap second) :
    ∃ automorphism : Aut finer.object,
      GaloisLevel.automorphismTransition diagram root refinement
          automorphism = 1 ∧
        (finer.automorphismAction.vertexAction automorphism first) = second := by
  rcases first with ⟨firstVertex, firstComponent⟩
  rcases second with ⟨secondVertex, secondComponent⟩
  have vertexEquality : firstVertex = secondVertex :=
    Sigma.mk.inj_iff.mp sameImage |>.1
  subst secondVertex
  letI := (diagram.vertexAnabelioid firstVertex).coverCategory
  letI := (diagram.vertexAnabelioid firstVertex).galoisCategory
  letI := (diagram.vertexAnabelioid firstVertex).fiberFunctor
  let firstPoint : (diagram.vertexAnabelioid firstVertex).fiber.obj
      (finer.object.vertexObject firstVertex) :=
    firstComponent.out
  let secondPoint : (diagram.vertexAnabelioid firstVertex).fiber.obj
      (finer.object.vertexObject firstVertex) :=
    secondComponent.out
  let firstImage : (diagram.vertexAnabelioid firstVertex).fiber.obj
      (coarser.object.vertexObject firstVertex) :=
    (rootFiber diagram firstVertex).map refinement.val firstPoint
  let secondImage : (diagram.vertexAnabelioid firstVertex).fiber.obj
      (coarser.object.vertexObject firstVertex) :=
    (rootFiber diagram firstVertex).map refinement.val secondPoint
  have componentEquality :
      EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.vertexAnabelioid firstVertex)
          (refinement.val.app firstVertex) firstComponent =
        EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.vertexAnabelioid firstVertex)
          (refinement.val.app firstVertex) secondComponent :=
    eq_of_heq (Sigma.mk.inj_iff.mp sameImage |>.2)
  rw [← Quotient.out_eq' firstComponent,
    ← Quotient.out_eq' secondComponent] at componentEquality
  change Quotient.mk'' firstImage = Quotient.mk'' secondImage at componentEquality
  have relation := Quotient.exact componentEquality.symm
  change secondImage ∈
      MulAction.orbit (Aut (diagram.vertexAnabelioid firstVertex).fiber)
        firstImage at relation
  obtain ⟨localAutomorphism, localEquality⟩ := relation
  let adjustedFirst : (diagram.vertexAnabelioid firstVertex).fiber.obj
      (finer.object.vertexObject firstVertex) :=
    localAutomorphism • firstPoint
  have adjustedImage :
      (rootFiber diagram firstVertex).map refinement.val adjustedFirst =
        secondImage := by
    change (diagram.vertexAnabelioid firstVertex).fiber.map
        (refinement.val.app firstVertex) (localAutomorphism • firstPoint) =
      secondImage
    change (diagram.vertexAnabelioid firstVertex).fiber.map
        (refinement.val.app firstVertex)
          (localAutomorphism.hom.app
            (finer.object.vertexObject firstVertex) firstPoint) = secondImage
    rw [← FintypeCat.comp_apply, ← localAutomorphism.hom.naturality]
    exact localEquality
  obtain ⟨automorphism, pointEquality, kernelEquality⟩ :=
    exists_kernelAutomorphism_of_fiber_eq diagram root refinement
      firstVertex adjustedFirst secondPoint adjustedImage
  refine ⟨automorphism, kernelEquality, ?_⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change EtaleFundamentalGroup.fiberComponentHomMap
      (diagram.vertexAnabelioid firstVertex)
      (automorphism.hom.app firstVertex) firstComponent = secondComponent
  rw [← Quotient.out_eq' secondComponent]
  have adjustedClass : Quotient.mk'' adjustedFirst = firstComponent := by
    rw [← Quotient.out_eq' firstComponent]
    apply Quotient.sound
    change adjustedFirst ∈
      MulAction.orbit (Aut (diagram.vertexAnabelioid firstVertex).fiber)
        firstPoint
    exact MulAction.mem_orbit _ localAutomorphism
  rw [← adjustedClass]
  change Quotient.mk''
      ((rootFiber diagram firstVertex).map automorphism.hom adjustedFirst) =
    Quotient.mk'' secondPoint
  exact congrArg Quotient.mk'' pointEquality

/-- The kernel of automorphism descent is transitive on every fiber of the
edge-component transition map. -/
theorem transitionEdge_kernel_transitive
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (first second : finer.semiGraph.Edge)
    (sameImage : (GaloisLevel.transition diagram root refinement).edgeMap
        first =
      (GaloisLevel.transition diagram root refinement).edgeMap second) :
    ∃ automorphism : Aut finer.object,
      GaloisLevel.automorphismTransition diagram root refinement
          automorphism = 1 ∧
        (finer.automorphismAction.edgeAction automorphism first) = second := by
  rcases first with ⟨firstEdge, firstComponent⟩
  rcases second with ⟨secondEdge, secondComponent⟩
  have edgeEquality : firstEdge = secondEdge :=
    Sigma.mk.inj_iff.mp sameImage |>.1
  subst secondEdge
  let reference := coverReferenceBranch diagram root firstEdge
  let pointed := diagram.branchMorphism reference.branch reference.abuts
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid reference.vertex).fiberFunctor
  letI := (diagram.edgeAnabelioid firstEdge).coverCategory
  letI := (diagram.edgeAnabelioid firstEdge).galoisCategory
  letI := (diagram.edgeAnabelioid firstEdge).fiberFunctor
  let firstPoint : (diagram.edgeAnabelioid firstEdge).fiber.obj
      (coverEdgeObject diagram root finer.object firstEdge) :=
    firstComponent.out
  let secondPoint : (diagram.edgeAnabelioid firstEdge).fiber.obj
      (coverEdgeObject diagram root finer.object firstEdge) :=
    secondComponent.out
  let edgeRefinement :=
    reference.pullback.map (refinement.val.app reference.vertex)
  let firstImage : (diagram.edgeAnabelioid firstEdge).fiber.obj
      (coverEdgeObject diagram root coarser.object firstEdge) :=
    (diagram.edgeAnabelioid firstEdge).fiber.map edgeRefinement firstPoint
  let secondImage : (diagram.edgeAnabelioid firstEdge).fiber.obj
      (coverEdgeObject diagram root coarser.object firstEdge) :=
    (diagram.edgeAnabelioid firstEdge).fiber.map edgeRefinement secondPoint
  have componentEquality :
      EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.edgeAnabelioid firstEdge) edgeRefinement firstComponent =
        EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.edgeAnabelioid firstEdge) edgeRefinement secondComponent :=
    eq_of_heq (Sigma.mk.inj_iff.mp sameImage |>.2)
  rw [← Quotient.out_eq' firstComponent,
    ← Quotient.out_eq' secondComponent] at componentEquality
  change Quotient.mk'' firstImage = Quotient.mk'' secondImage at componentEquality
  have relation := Quotient.exact componentEquality.symm
  change secondImage ∈
      MulAction.orbit (Aut (diagram.edgeAnabelioid firstEdge).fiber)
        firstImage at relation
  obtain ⟨localAutomorphism, localEquality⟩ := relation
  let adjustedFirst : (diagram.edgeAnabelioid firstEdge).fiber.obj
      (coverEdgeObject diagram root finer.object firstEdge) :=
    localAutomorphism • firstPoint
  have adjustedImage :
      (diagram.edgeAnabelioid firstEdge).fiber.map edgeRefinement
          adjustedFirst = secondImage := by
    change (diagram.edgeAnabelioid firstEdge).fiber.map edgeRefinement
        (localAutomorphism.hom.app
          (coverEdgeObject diagram root finer.object firstEdge) firstPoint) =
      secondImage
    dsimp only [edgeRefinement]
    change (localAutomorphism.hom.app
          (reference.pullback.obj
            (finer.object.vertexObject reference.vertex)) ≫
        (diagram.edgeAnabelioid firstEdge).fiber.map
          (reference.pullback.map
            (refinement.val.app reference.vertex))) firstPoint = secondImage
    rw [← localAutomorphism.hom.naturality]
    exact localEquality
  let adjustedVertexPoint :
      (rootFiber diagram reference.vertex).obj finer.object :=
    pointed.fiberIso.hom.app
      (finer.object.vertexObject reference.vertex) adjustedFirst
  let secondVertexPoint :
      (rootFiber diagram reference.vertex).obj finer.object :=
    pointed.fiberIso.hom.app
      (finer.object.vertexObject reference.vertex) secondPoint
  have vertexImageEquality :
      (rootFiber diagram reference.vertex).map refinement.val
          adjustedVertexPoint =
        (rootFiber diagram reference.vertex).map refinement.val
          secondVertexPoint := by
    have adjustedNaturality :
        pointed.fiberIso.hom.app
              (coarser.object.vertexObject reference.vertex)
              ((diagram.edgeAnabelioid firstEdge).fiber.map edgeRefinement
                adjustedFirst) =
            (rootFiber diagram reference.vertex).map refinement.val
              adjustedVertexPoint := by
      simpa only [edgeRefinement, adjustedVertexPoint,
        FintypeCat.comp_apply] using
          ConcreteCategory.congr_hom
            (pointed.fiberIso.hom.naturality
              (refinement.val.app reference.vertex)) adjustedFirst
    have secondNaturality :
        pointed.fiberIso.hom.app
              (coarser.object.vertexObject reference.vertex) secondImage =
            (rootFiber diagram reference.vertex).map refinement.val
              secondVertexPoint := by
      simpa only [edgeRefinement, secondImage, secondVertexPoint,
        FintypeCat.comp_apply] using
          ConcreteCategory.congr_hom
            (pointed.fiberIso.hom.naturality
              (refinement.val.app reference.vertex)) secondPoint
    exact adjustedNaturality.symm.trans <|
      congrArg
        (fun point ↦ pointed.fiberIso.hom.app
          (coarser.object.vertexObject reference.vertex) point)
        adjustedImage |>.trans secondNaturality
  obtain ⟨automorphism, vertexPointEquality, kernelEquality⟩ :=
    exists_kernelAutomorphism_of_fiber_eq diagram root refinement
      reference.vertex adjustedVertexPoint secondVertexPoint
        vertexImageEquality
  have edgePointEquality :
      (diagram.edgeAnabelioid firstEdge).fiber.map
          (reference.pullback.map
            (automorphism.hom.app reference.vertex)) adjustedFirst =
        secondPoint := by
    apply (ConcreteCategory.bijective_of_isIso
      (pointed.fiberIso.hom.app
        (finer.object.vertexObject reference.vertex))).1
    have naturalityPoint :
        pointed.fiberIso.hom.app
              (finer.object.vertexObject reference.vertex)
              ((diagram.edgeAnabelioid firstEdge).fiber.map
                (reference.pullback.map
                  (automorphism.hom.app reference.vertex)) adjustedFirst) =
            (rootFiber diagram reference.vertex).map automorphism.hom
              adjustedVertexPoint := by
      simpa only [adjustedVertexPoint, FintypeCat.comp_apply] using
        ConcreteCategory.congr_hom
          (pointed.fiberIso.hom.naturality
            (automorphism.hom.app reference.vertex)) adjustedFirst
    exact naturalityPoint.trans vertexPointEquality
  refine ⟨automorphism, kernelEquality, ?_⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change EtaleFundamentalGroup.fiberComponentHomMap
      (diagram.edgeAnabelioid firstEdge)
      (reference.pullback.map
        (automorphism.hom.app reference.vertex)) firstComponent =
    secondComponent
  rw [← Quotient.out_eq' secondComponent]
  have adjustedClass : Quotient.mk'' adjustedFirst = firstComponent := by
    rw [← Quotient.out_eq' firstComponent]
    apply Quotient.sound
    change adjustedFirst ∈
      MulAction.orbit (Aut (diagram.edgeAnabelioid firstEdge).fiber)
        firstPoint
    exact MulAction.mem_orbit _ localAutomorphism
  rw [← adjustedClass]
  change Quotient.mk''
      ((diagram.edgeAnabelioid firstEdge).fiber.map
        (reference.pullback.map
          (automorphism.hom.app reference.vertex)) adjustedFirst) =
    Quotient.mk'' secondPoint
  exact congrArg Quotient.mk'' edgePointEquality

/-- Kernel symmetries are transitive on every fiber of the faithful-incidence
refinement map. -/
theorem refinementIncidenceMap_kernel_transitive
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (first second : IncidenceNode finer.semiGraph)
    (sameImage : RefinementIncidenceMap diagram root refinement first =
      RefinementIncidenceMap diagram root refinement second) :
    ∃ automorphism : Aut finer.object,
      GaloisLevel.automorphismTransition diagram root refinement
          automorphism = 1 ∧
        IncidenceNode.incidencePerm finer.semiGraph
          finer.automorphismAction automorphism first = second := by
  cases first with
  | vertex first =>
      cases second with
      | vertex second =>
          cases first with
          | inl first =>
              cases second with
              | inl second =>
                  have vertexImage :
                      (GaloisLevel.transition diagram root refinement).vertexMap
                          first =
                        (GaloisLevel.transition diagram root refinement).vertexMap
                          second := by
                    exact Sum.inl.inj <| IncidenceNode.vertex.inj sameImage
                  obtain ⟨automorphism, kernelEquality, pointEquality⟩ :=
                    transitionVertex_kernel_transitive diagram root refinement
                      first second vertexImage
                  refine ⟨automorphism, kernelEquality, ?_⟩
                  rw [IncidenceNode.incidencePerm_vertex]
                  exact congrArg (fun value ↦
                    IncidenceNode.vertex (Sum.inl value)) pointEquality
              | inr second =>
                  cases IncidenceNode.vertex.inj sameImage
          | inr first =>
              cases second with
              | inl second =>
                  cases IncidenceNode.vertex.inj sameImage
              | inr second =>
                  have branchImage :
                      (GaloisLevel.transition diagram root refinement).totalBranchMap
                          first.1 =
                        (GaloisLevel.transition diagram root refinement).totalBranchMap
                          second.1 := by
                    exact congrArg Subtype.val <| Sum.inr.inj <|
                      IncidenceNode.vertex.inj sameImage
                  have edgeImage :
                      (GaloisLevel.transition diagram root refinement).edgeMap
                          first.1.1 =
                        (GaloisLevel.transition diagram root refinement).edgeMap
                          second.1.1 :=
                    Sigma.mk.inj_iff.mp branchImage |>.1
                  obtain ⟨automorphism, kernelEquality, edgeEquality⟩ :=
                    transitionEdge_kernel_transitive diagram root refinement
                      first.1.1 second.1.1 edgeImage
                  refine ⟨automorphism, kernelEquality, ?_⟩
                  rw [IncidenceNode.incidencePerm_vertex]
                  apply congrArg (fun value ↦
                    IncidenceNode.vertex (Sum.inr value))
                  apply Subtype.ext
                  apply Sigma.ext edgeEquality
                  exact Sigma.mk.inj_iff.mp branchImage |>.2
      | edge second => cases sameImage
      | branch second => cases sameImage
  | edge first =>
      cases second with
      | vertex second => cases sameImage
      | edge second =>
          have edgeImage :
              (GaloisLevel.transition diagram root refinement).edgeMap first =
                (GaloisLevel.transition diagram root refinement).edgeMap
                  second :=
            IncidenceNode.edge.inj sameImage
          obtain ⟨automorphism, kernelEquality, edgeEquality⟩ :=
            transitionEdge_kernel_transitive diagram root refinement
              first second edgeImage
          refine ⟨automorphism, kernelEquality, ?_⟩
          rw [IncidenceNode.incidencePerm_edge]
          exact congrArg IncidenceNode.edge edgeEquality
      | branch second => cases sameImage
  | branch first =>
      cases second with
      | vertex second => cases sameImage
      | edge second => cases sameImage
      | branch second =>
          have branchImage :
              (GaloisLevel.transition diagram root refinement).totalBranchMap
                  first =
                (GaloisLevel.transition diagram root refinement).totalBranchMap
                  second :=
            IncidenceNode.branch.inj sameImage
          have edgeImage :
              (GaloisLevel.transition diagram root refinement).edgeMap
                  first.1 =
                (GaloisLevel.transition diagram root refinement).edgeMap
                  second.1 :=
            Sigma.mk.inj_iff.mp branchImage |>.1
          obtain ⟨automorphism, kernelEquality, edgeEquality⟩ :=
            transitionEdge_kernel_transitive diagram root refinement
              first.1 second.1 edgeImage
          refine ⟨automorphism, kernelEquality, ?_⟩
          rw [IncidenceNode.incidencePerm_branch]
          apply congrArg IncidenceNode.branch
          apply Sigma.ext edgeEquality
          exact Sigma.mk.inj_iff.mp branchImage |>.2

/-- At one Galois level, the stabilizer of an incidence node is transitive on
the neighboring lifts of any fixed base-incidence neighbor. -/
theorem incidenceNeighbor_stabilizer_transitive
    (level : GaloisLevel diagram root)
    (center first second : IncidenceNode level.semiGraph)
    (firstAdjacent : (IncidenceGraph diagram root level).Adj center first)
    (secondAdjacent : (IncidenceGraph diagram root level).Adj center second)
    (sameBase : BaseIncidenceProjection diagram root level first =
      BaseIncidenceProjection diagram root level second) :
    ∃ automorphism : Aut level.object,
      IncidenceNode.incidencePerm level.semiGraph level.automorphismAction
          automorphism center = center ∧
        IncidenceNode.incidencePerm level.semiGraph level.automorphismAction
          automorphism first = second := by
  cases center with
  | vertex center =>
      cases first with
      | vertex first =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | edge first =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | branch first =>
          cases second with
          | vertex second => cases sameBase
          | edge second => cases sameBase
          | branch second =>
              have branchImage : level.projection.totalBranchMap first =
                  level.projection.totalBranchMap second :=
                IncidenceNode.branch.inj sameBase
              have edgeImage : level.projection.edgeMap first.1 =
                  level.projection.edgeMap second.1 :=
                Sigma.mk.inj_iff.mp branchImage |>.1
              obtain ⟨automorphism, edgeEquality⟩ :=
                GaloisLevel.edgeAction_transitive_on_projection_fiber
                  diagram root level first.1 second.1 edgeImage
              have branchEquality :
                  IncidenceNode.incidencePerm level.semiGraph
                      level.automorphismAction automorphism
                      (IncidenceNode.branch first) =
                    IncidenceNode.branch second := by
                rw [IncidenceNode.incidencePerm_branch]
                apply congrArg IncidenceNode.branch
                apply Sigma.ext edgeEquality
                exact Sigma.mk.inj_iff.mp branchImage |>.2
              have mappedAdjacent :
                  (IncidenceGraph diagram root level).Adj
                    (IncidenceNode.incidencePerm level.semiGraph
                      level.automorphismAction automorphism
                      (IncidenceNode.vertex center))
                    (IncidenceNode.incidencePerm level.semiGraph
                      level.automorphismAction automorphism
                      (IncidenceNode.branch first)) :=
                (IncidenceNode.incidenceIso level.semiGraph
                  level.automorphismAction automorphism).map_rel_iff.mpr
                    firstAdjacent
              have mappedCoincidence :=
                (IncidenceNode.vertex_branch_adj level.semiGraph _ _).mp <| by
                  rw [branchEquality] at mappedAdjacent
                  exact mappedAdjacent
              have centerCoincidence :=
                (IncidenceNode.vertex_branch_adj level.semiGraph _ _).mp
                  secondAdjacent
              have centerEquality :
                  IncidenceNode.incidencePerm level.semiGraph
                      level.automorphismAction automorphism
                      (IncidenceNode.vertex center) =
                    IncidenceNode.vertex center := by
                apply congrArg IncidenceNode.vertex
                exact Option.some.inj <|
                  mappedCoincidence.symm.trans centerCoincidence
              exact ⟨automorphism, centerEquality, branchEquality⟩
  | edge center =>
      cases first with
      | vertex first =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | edge first =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | branch first =>
          cases second with
          | vertex second => cases sameBase
          | edge second => cases sameBase
          | branch second =>
              have firstSupport :=
                (IncidenceNode.edge_branch_adj level.semiGraph center first).mp
                  firstAdjacent
              have secondSupport :=
                (IncidenceNode.edge_branch_adj level.semiGraph center second).mp
                  secondAdjacent
              have branchImage : level.projection.totalBranchMap first =
                  level.projection.totalBranchMap second :=
                IncidenceNode.branch.inj sameBase
              have branchEquality : first = second := by
                rcases first with ⟨firstEdge, firstBranch⟩
                rcases second with ⟨secondEdge, secondBranch⟩
                change firstEdge = center at firstSupport
                change secondEdge = center at secondSupport
                subst firstEdge
                subst secondEdge
                exact Sigma.ext (by rfl)
                  (Sigma.mk.inj_iff.mp branchImage |>.2)
              subst second
              exact ⟨1, by simp, by simp⟩
  | branch center =>
      cases first with
      | branch first =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at firstAdjacent
      | edge first =>
          cases second with
          | vertex second => cases sameBase
          | branch second => cases sameBase
          | edge second =>
              have firstSupport :=
                (IncidenceNode.branch_edge_adj level.semiGraph center first).mp
                  firstAdjacent
              have secondSupport :=
                (IncidenceNode.branch_edge_adj level.semiGraph center second).mp
                  secondAdjacent
              have edgeEquality : first = second :=
                firstSupport.symm.trans secondSupport
              exact ⟨1, by simp, by simpa using edgeEquality⟩
      | vertex first =>
          cases second with
          | edge second => cases sameBase
          | branch second => cases sameBase
          | vertex second =>
              have firstCoincidence :=
                (IncidenceNode.branch_vertex_adj level.semiGraph center first).mp
                  firstAdjacent
              have secondCoincidence :=
                (IncidenceNode.branch_vertex_adj level.semiGraph center second).mp
                  secondAdjacent
              have vertexEquality : first = second :=
                Option.some.inj <| firstCoincidence.symm.trans secondCoincidence
              exact ⟨1, by simp, by simpa using vertexEquality⟩

/-- The faithful-incidence projection of a finite Galois level lifts every
adjacent base node from a prescribed node upstairs. -/
theorem baseIncidenceProjection_isLocallySurjective
    (level : GaloisLevel diagram root) :
    UniversalVertex.IsLocallySurjective
      (IncidenceGraph diagram root level) (BaseIncidenceGraph diagram)
      (BaseIncidenceProjection diagram root level) := by
  intro center target adjacent
  cases center with
  | vertex center =>
      cases center with
      | inl center =>
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_original] at adjacent
          cases target with
          | vertex target =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at adjacent
          | edge target =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at adjacent
          | branch target =>
              rcases center with ⟨baseVertex, component⟩
              have targetCoincidence :=
                (IncidenceNode.vertex_branch_adj diagram.base
                  (Sum.inl baseVertex) target).mp adjacent
              have baseCoincidence :
                  diagram.base.coincidence target.1 target.2 =
                    some baseVertex := by
                cases coincidence :
                    diagram.base.coincidence target.1 target.2 with
                | none =>
                    rw [diagram.base.compactification_coincidence_of_none
                      coincidence] at targetCoincidence
                    cases targetCoincidence
                | some vertex =>
                    rw [diagram.base.compactification_coincidence_of_some
                      coincidence] at targetCoincidence
                    exact congrArg some <|
                      Sum.inl.inj (Option.some.inj targetCoincidence)
              let incident : diagram.IncidentBranch target.1 :=
                ⟨target.2, baseVertex, baseCoincidence⟩
              obtain ⟨edgeComponent, componentEquality⟩ :=
                coverComponentMap_surjective diagram root level.object
                  incident component
              let sourceBranch :
                  (LevelSemiGraph diagram root level).TotalBranch :=
                ⟨⟨target.1, edgeComponent⟩, target.2⟩
              refine ⟨IncidenceNode.branch sourceBranch, ?_, ?_⟩
              · apply (IncidenceNode.vertex_branch_adj
                    (LevelSemiGraph diagram root level) _ _).mpr
                have liftedCoincidence :
                    (LevelSemiGraph diagram root level).coincidence
                        ⟨target.1, edgeComponent⟩ target.2 =
                      some ⟨baseVertex,
                        coverComponentMap diagram root level.object incident
                          edgeComponent⟩ :=
                  finiteEtaleCoverSemiGraph_coincidence_of_some
                    diagram root level.object baseCoincidence
                rw [(LevelSemiGraph diagram root level).compactification_coincidence_of_some
                  liftedCoincidence]
                exact congrArg some <| congrArg Sum.inl <|
                  Sigma.ext rfl (heq_of_eq componentEquality)
              · rw [IncidenceNode.properIncidenceGraphHom_apply,
                  IncidenceNode.properMap_branch]
                rfl
      | inr center =>
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary] at adjacent
          cases target with
          | vertex target =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at adjacent
          | edge target =>
              simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
                SimpleGraph.fromRel_adj] at adjacent
          | branch target =>
              let mappedBoundary := IncidenceNode.nonVerticialMap
                (LevelSemiGraph diagram root level) level.projection
                  level.projection_isProper center
              have targetCoincidence :=
                (IncidenceNode.vertex_branch_adj diagram.base
                  (Sum.inr mappedBoundary) target).mp adjacent
              have targetEquality :
                  target = level.projection.totalBranchMap center.1 := by
                cases coincidence : diagram.base.coincidenceTotal target with
                | some vertex =>
                    rw [diagram.base.compactification_coincidence_of_some
                      coincidence] at targetCoincidence
                    cases targetCoincidence
                | none =>
                    rw [diagram.base.compactification_coincidence_of_none
                      coincidence] at targetCoincidence
                    exact congrArg Subtype.val <|
                      (Sum.inr.inj <|
                        Option.some.inj targetCoincidence)
              refine ⟨IncidenceNode.branch center.1, ?_, ?_⟩
              · exact (IncidenceNode.vertex_branch_adj
                    (LevelSemiGraph diagram root level) _ _).mpr <|
                  (LevelSemiGraph diagram root level).compactification_coincidence_of_none
                    center.2
              · rw [IncidenceNode.properIncidenceGraphHom_apply,
                  IncidenceNode.properMap_branch, targetEquality]
  | edge center =>
      rw [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge] at adjacent
      cases target with
      | vertex target =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | edge target =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | branch target =>
          have targetSupport :=
            (IncidenceNode.edge_branch_adj diagram.base _ _).mp adjacent
          rcases target with ⟨targetEdge, targetBranch⟩
          change targetEdge = level.projection.edgeMap center at targetSupport
          subst targetEdge
          let sourceBranch :
              (LevelSemiGraph diagram root level).TotalBranch :=
            ⟨center, (level.projection.branchEquiv center).symm targetBranch⟩
          refine ⟨IncidenceNode.branch sourceBranch, ?_, ?_⟩
          · exact (IncidenceNode.edge_branch_adj
              (LevelSemiGraph diagram root level) _ _).mpr rfl
          · rw [IncidenceNode.properIncidenceGraphHom_apply,
              IncidenceNode.properMap_branch]
            apply congrArg IncidenceNode.branch
            apply Sigma.ext rfl
            exact heq_of_eq <|
              (level.projection.branchEquiv center).apply_symm_apply targetBranch
  | branch center =>
      rw [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch] at adjacent
      cases target with
      | edge target =>
          have targetSupport :=
            (IncidenceNode.branch_edge_adj diagram.base _ _).mp adjacent
          refine ⟨IncidenceNode.edge center.1, ?_, ?_⟩
          · exact (IncidenceNode.branch_edge_adj
              (LevelSemiGraph diagram root level) _ _).mpr rfl
          · rw [IncidenceNode.properIncidenceGraphHom_apply,
              IncidenceNode.properMap_edge]
            exact congrArg IncidenceNode.edge targetSupport
      | branch target =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | vertex target =>
          have targetCoincidence :=
            (IncidenceNode.branch_vertex_adj diagram.base _ _).mp adjacent
          cases sourceCoincidence :
              (LevelSemiGraph diagram root level).coincidenceTotal center with
          | some vertex =>
              let source := IncidenceNode.vertex (Sum.inl vertex)
              have sourceAdjacent :
                  (IncidenceGraph diagram root level).Adj
                    (IncidenceNode.branch center) source :=
                (IncidenceNode.branch_vertex_adj
                  (LevelSemiGraph diagram root level) _ _).mpr <| by
                    rw [(LevelSemiGraph diagram root level).compactification_coincidence_of_some
                      sourceCoincidence]
                    rfl
              refine ⟨source, sourceAdjacent, ?_⟩
              have mappedAdjacent :=
                (BaseIncidenceProjection diagram root level).map_rel
                  sourceAdjacent
              have mappedCoincidence :=
                (IncidenceNode.branch_vertex_adj diagram.base _ _).mp
                  mappedAdjacent
              apply congrArg IncidenceNode.vertex
              exact Option.some.inj <|
                mappedCoincidence.symm.trans targetCoincidence
          | none =>
              let boundary :
                  (LevelSemiGraph diagram root level).NonVerticialBranch :=
                ⟨center, sourceCoincidence⟩
              let source := IncidenceNode.vertex (Sum.inr boundary)
              have sourceAdjacent :
                  (IncidenceGraph diagram root level).Adj
                    (IncidenceNode.branch center) source :=
                (IncidenceNode.branch_vertex_adj
                  (LevelSemiGraph diagram root level) _ _).mpr <| by
                    rw [(LevelSemiGraph diagram root level).compactification_coincidence_of_none
                      sourceCoincidence]
                    rfl
              refine ⟨source, sourceAdjacent, ?_⟩
              have mappedAdjacent :=
                (BaseIncidenceProjection diagram root level).map_rel
                  sourceAdjacent
              have mappedCoincidence :=
                (IncidenceNode.branch_vertex_adj diagram.base _ _).mp
                  mappedAdjacent
              apply congrArg IncidenceNode.vertex
              exact Option.some.inj <|
                mappedCoincidence.symm.trans targetCoincidence

/-- A pointed Galois refinement lifts every adjacent coarser incidence node
from a prescribed finer incidence node. -/
theorem refinementIncidenceMap_isLocallySurjective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    UniversalVertex.IsLocallySurjective
      (IncidenceGraph diagram root finer) (IncidenceGraph diagram root coarser)
      (RefinementIncidenceMap diagram root refinement) := by
  intro center target adjacent
  have baseAdjacent :
      (BaseIncidenceGraph diagram).Adj
        (BaseIncidenceProjection diagram root finer center)
        (BaseIncidenceProjection diagram root coarser target) := by
    have mapped :=
      (BaseIncidenceProjection diagram root coarser).map_rel adjacent
    rw [baseIncidenceProjection_refinement diagram root refinement center] at mapped
    exact mapped
  obtain ⟨source, sourceAdjacent, sourceBase⟩ :=
    baseIncidenceProjection_isLocallySurjective diagram root finer
      baseAdjacent
  have mappedAdjacent :
      (IncidenceGraph diagram root coarser).Adj
        (RefinementIncidenceMap diagram root refinement center)
        (RefinementIncidenceMap diagram root refinement source) :=
    (RefinementIncidenceMap diagram root refinement).map_rel sourceAdjacent
  have mappedSourceBase :
      BaseIncidenceProjection diagram root coarser
          (RefinementIncidenceMap diagram root refinement source) =
        BaseIncidenceProjection diagram root coarser target := by
    rw [baseIncidenceProjection_refinement diagram root refinement source,
      sourceBase]
  obtain ⟨targetAutomorphism, fixesCenter, mapsSource⟩ :=
    incidenceNeighbor_stabilizer_transitive diagram root coarser
      (RefinementIncidenceMap diagram root refinement center)
      (RefinementIncidenceMap diagram root refinement source) target
      mappedAdjacent adjacent mappedSourceBase
  obtain ⟨sourceAutomorphism, automorphismMaps⟩ :=
    GaloisLevel.automorphismTransition_surjective diagram root refinement
      targetAutomorphism
  have transformedCenterImage :
      RefinementIncidenceMap diagram root refinement
          (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
            sourceAutomorphism center) =
        RefinementIncidenceMap diagram root refinement center := by
    rw [refinement_incidence_commutes diagram root refinement,
      automorphismMaps, fixesCenter]
  obtain ⟨kernelAutomorphism, kernelMaps, correctsCenter⟩ :=
    refinementIncidenceMap_kernel_transitive diagram root refinement
      (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
        sourceAutomorphism center)
      center transformedCenterImage
  let liftedSource :=
    IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
      sourceAutomorphism source
  let correctedSource :=
    IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
      kernelAutomorphism liftedSource
  refine ⟨correctedSource, ?_, ?_⟩
  · have liftedAdjacent :
        (IncidenceGraph diagram root finer).Adj
          (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
            sourceAutomorphism center) liftedSource :=
      (IncidenceNode.incidenceIso finer.semiGraph finer.automorphismAction
        sourceAutomorphism).map_rel_iff.mpr sourceAdjacent
    have correctedAdjacent :
        (IncidenceGraph diagram root finer).Adj
          (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
            kernelAutomorphism
            (IncidenceNode.incidencePerm finer.semiGraph
              finer.automorphismAction sourceAutomorphism center))
          correctedSource :=
      (IncidenceNode.incidenceIso finer.semiGraph finer.automorphismAction
        kernelAutomorphism).map_rel_iff.mpr liftedAdjacent
    rw [correctsCenter] at correctedAdjacent
    exact correctedAdjacent
  · change RefinementIncidenceMap diagram root refinement
        (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
          kernelAutomorphism
          (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
            sourceAutomorphism source)) = target
    rw [refinement_incidence_commutes diagram root refinement,
      kernelMaps, IncidenceNode.incidencePerm_one,
      refinement_incidence_commutes diagram root refinement,
      automorphismMaps, mapsSource]
    rfl

/-- The canonical map between the two reduced-walk universal trees is
surjective. -/
theorem refinementTreeMap_surjective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    Function.Surjective (RefinementTreeMap diagram root refinement) := by
  apply Function.Surjective.comp
    (UniversalVertex.castRoot_surjective
      (IncidenceGraph diagram root coarser)
      (refinementIncidenceMap_root diagram root refinement))
  exact UniversalVertex.mapHom_surjective_of_locallySurjective
    (IncidenceGraph diagram root finer) (IncidenceRoot diagram root finer)
    (IncidenceGraph diagram root coarser)
    (RefinementIncidenceMap diagram root refinement)
    (refinementIncidenceMap_isLocallySurjective diagram root refinement)

/-- Every complete coarser deck transformation lifts across a pointed Galois
refinement. -/
theorem deckTransition_surjective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    Function.Surjective (deckTransition diagram root refinement) := by
  intro targetTransformation
  let targetRoot := IncidenceRoot diagram root coarser
  let targetBase :=
    UniversalVertex.base (IncidenceGraph diagram root coarser) targetRoot
  let targetSymmetry :=
    UniversalVertex.CompositeDeckTransformation.baseSymmetry
      targetTransformation
  let targetBaseImage :=
    UniversalVertex.CompositeDeckTransformation.treePerm
      targetTransformation targetBase
  obtain ⟨sourceSymmetry, symmetryMaps⟩ :=
    GaloisLevel.automorphismTransition_surjective diagram root refinement
      targetSymmetry
  obtain ⟨sourceBaseImage, baseImageMaps⟩ :=
    refinementTreeMap_surjective diagram root refinement targetBaseImage
  have endpointImagesEqual :
      RefinementIncidenceMap diagram root refinement
          (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
            sourceSymmetry (IncidenceRoot diagram root finer)) =
        RefinementIncidenceMap diagram root refinement
          sourceBaseImage.endpoint := by
    calc
      RefinementIncidenceMap diagram root refinement
          (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
            sourceSymmetry (IncidenceRoot diagram root finer)) =
          IncidenceNode.incidencePerm coarser.semiGraph
            coarser.automorphismAction targetSymmetry
              (RefinementIncidenceMap diagram root refinement
                (IncidenceRoot diagram root finer)) := by
                  rw [refinement_incidence_commutes diagram root refinement,
                    symmetryMaps]
      _ = IncidenceNode.incidencePerm coarser.semiGraph
            coarser.automorphismAction targetSymmetry targetRoot := by
              rw [refinementIncidenceMap_root diagram root refinement]
      _ = targetBaseImage.endpoint := by
              exact (UniversalVertex.CompositeDeckTransformation.endpoint_apply
                targetTransformation targetBase).symm
      _ = (RefinementTreeMap diagram root refinement
            sourceBaseImage).endpoint :=
              congrArg
                (fun point : IncidenceTreeVertex diagram root coarser ↦
                  point.endpoint) baseImageMaps.symm
      _ = RefinementIncidenceMap diagram root refinement
            sourceBaseImage.endpoint :=
              refinementTreeMap_endpoint diagram root refinement sourceBaseImage
  obtain ⟨kernelSymmetry, kernelMaps, endpointCorrection⟩ :=
    refinementIncidenceMap_kernel_transitive diagram root refinement
      (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
        sourceSymmetry (IncidenceRoot diagram root finer))
      sourceBaseImage.endpoint endpointImagesEqual
  let correctedSymmetry := kernelSymmetry * sourceSymmetry
  have correctedSymmetryMaps :
      GaloisLevel.automorphismTransition diagram root refinement
          correctedSymmetry = targetSymmetry := by
    change GaloisLevel.automorphismTransition diagram root refinement
        (kernelSymmetry * sourceSymmetry) = targetSymmetry
    rw [map_mul, kernelMaps, symmetryMaps, one_mul]
  have correctedEndpoint :
      (IncidenceActionHom diagram root finer correctedSymmetry).1
          (IncidenceRoot diagram root finer) = sourceBaseImage.endpoint := by
    change IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
        correctedSymmetry (IncidenceRoot diagram root finer) =
      sourceBaseImage.endpoint
    change IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
        (kernelSymmetry * sourceSymmetry) (IncidenceRoot diagram root finer) =
      sourceBaseImage.endpoint
    rw [IncidenceNode.incidencePerm_mul, Equiv.Perm.mul_apply]
    exact endpointCorrection
  let sourceBase := UniversalVertex.base
    (IncidenceGraph diagram root finer) (IncidenceRoot diagram root finer)
  let sourceTransformation : DeckGroup diagram root finer :=
    UniversalVertex.CompositeDeckTransformation.between
      correctedSymmetry sourceBase sourceBaseImage correctedEndpoint
  refine ⟨sourceTransformation, ?_⟩
  apply UniversalVertex.CompositeDeckTransformation.encoding_injective targetBase
  apply Prod.ext
  · change TransitionedSymmetry diagram root refinement
        sourceTransformation = targetSymmetry
    change GaloisLevel.automorphismTransition diagram root refinement
        correctedSymmetry = targetSymmetry
    exact correctedSymmetryMaps
  · change UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransitionToFun diagram root refinement sourceTransformation)
          targetBase = targetBaseImage
    rw [deckTransitionToFun_base]
    change RefinementTreeMap diagram root refinement
        (UniversalVertex.CompositeDeckTransformation.treePerm
          sourceTransformation sourceBase) = targetBaseImage
    rw [UniversalVertex.CompositeDeckTransformation.between_apply_first]
    exact baseImageMaps

end SourceGaloisCombinatorialUniversalCover

end SourceCombinatorialUniversalCover

end Iut
