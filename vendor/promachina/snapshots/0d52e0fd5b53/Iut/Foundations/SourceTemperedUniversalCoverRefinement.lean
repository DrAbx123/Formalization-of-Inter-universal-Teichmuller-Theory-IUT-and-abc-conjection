/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedFullCoverClassification

/-!
# Refinement maps between geometric tempered universal covers

The inverse system in *Semi-graphs of Anabelioids*, Proposition 3.6(ii), has
already been constructed on finite Galois levels, universal incidence trees,
and complete deck groups.  This file records the induced maps on lifted
components and retained finite points.  It then packages the literal geometric
universal covers into a lawful cofiltered functor by reusing geometric
domination, normalizing at the distinguished root point, and applying pointed
uniqueness for the identity and composition laws.  The constituent formulas
are assembled through the branch-gluing square and proved equivariant for the
finite-level deck transition maps.
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

namespace SourceTemperoidComponentFamily

/-- A finite equivariant map and a compatible map of selected orbit indices
induce a morphism between the corresponding repeated component families. -/
noncomputable def map
    {G : ProfiniteGrp.{u}}
    {source target : ContAction FintypeCat.{u} G}
    (arrow : source ⟶ target)
    {SourceIndex TargetIndex : Type u}
    [Countable SourceIndex] [Countable TargetIndex]
    (sourceComponent : SourceIndex → SourceActionComponent G source)
    (targetComponent : TargetIndex → SourceActionComponent G target)
    (indexMap : SourceIndex → TargetIndex)
    (componentCompatibility : ∀ index,
      SourceSemiGraphOfAnabelioids.CovObject.actionComponentMap
          ((SourceTemperoidAction.finiteInclusion G).map arrow)
          (sourceComponent index) =
        targetComponent (indexMap index)) :
    sourceTemperoidComponentFamilyAction
        G source SourceIndex sourceComponent ⟶
      sourceTemperoidComponentFamilyAction
        G target TargetIndex targetComponent := by
  let carrierMap :
      SourceTemperoidComponentFamilyCarrier
          G source SourceIndex sourceComponent →
      SourceTemperoidComponentFamilyCarrier
          G target TargetIndex targetComponent := fun point ↦
    ⟨indexMap point.1,
      ⟨arrow.hom.hom point.2.1, by
        change SourceSemiGraphOfAnabelioids.CovObject.actionComponentMap
            ((SourceTemperoidAction.finiteInclusion G).map arrow)
              (Quotient.mk'' point.2.1) = _
        exact (congrArg
          (SourceSemiGraphOfAnabelioids.CovObject.actionComponentMap
            ((SourceTemperoidAction.finiteInclusion G).map arrow))
          point.2.2).trans (componentCompatibility point.1)⟩⟩
  exact CategoryTheory.ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk carrierMap
      comm := fun element ↦ by
        apply CategoryTheory.ConcreteCategory.hom_ext
        intro point
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Subtype.ext
          exact CategoryTheory.ConcreteCategory.congr_hom
            (arrow.hom.comm element) point.2.1 }

@[simp]
theorem map_apply_index
    {G : ProfiniteGrp.{u}}
    {source target : ContAction FintypeCat.{u} G}
    (arrow : source ⟶ target)
    {SourceIndex TargetIndex : Type u}
    [Countable SourceIndex] [Countable TargetIndex]
    (sourceComponent : SourceIndex → SourceActionComponent G source)
    (targetComponent : TargetIndex → SourceActionComponent G target)
    (indexMap : SourceIndex → TargetIndex)
    (componentCompatibility : ∀ index,
      SourceSemiGraphOfAnabelioids.CovObject.actionComponentMap
          ((SourceTemperoidAction.finiteInclusion G).map arrow)
          (sourceComponent index) =
        targetComponent (indexMap index))
    (point : SourceTemperoidComponentFamilyCarrier
      G source SourceIndex sourceComponent) :
    ((map arrow sourceComponent targetComponent indexMap
      componentCompatibility).hom.hom point).1 = indexMap point.1 :=
  rfl

@[simp]
theorem map_apply_value
    {G : ProfiniteGrp.{u}}
    {source target : ContAction FintypeCat.{u} G}
    (arrow : source ⟶ target)
    {SourceIndex TargetIndex : Type u}
    [Countable SourceIndex] [Countable TargetIndex]
    (sourceComponent : SourceIndex → SourceActionComponent G source)
    (targetComponent : TargetIndex → SourceActionComponent G target)
    (indexMap : SourceIndex → TargetIndex)
    (componentCompatibility : ∀ index,
      SourceSemiGraphOfAnabelioids.CovObject.actionComponentMap
          ((SourceTemperoidAction.finiteInclusion G).map arrow)
          (sourceComponent index) =
        targetComponent (indexMap index))
    (point : SourceTemperoidComponentFamilyCarrier
      G source SourceIndex sourceComponent) :
    ((map arrow sourceComponent targetComponent indexMap
      componentCompatibility).hom.hom point).2.1 = arrow.hom.hom point.2.1 :=
  rfl

end SourceTemperoidComponentFamily

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

open SourceCombinatorialUniversalCover
open SourceSemiGraphOfAnabelioids.GluedObject
open SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
open SourceSemiGraphOfAnabelioids.CovObject
open SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)

/-- A pointed Galois refinement is constituentwise surjective after finite
temperification. -/
theorem refinementVertexMap_surjective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : diagram.base.Vertex) :
    Function.Surjective
      ((finiteCovMap diagram root refinement.val).app vertex).hom.hom := by
  letI : CategoryTheory.GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : CategoryTheory.PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  letI : CategoryTheory.PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : CategoryTheory.PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  haveI : CategoryTheory.Epi refinement.val :=
    CategoryTheory.PreGaloisCategory.epi_of_nonempty_of_isConnected
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root)
      refinement.val
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  letI := (diagram.vertexAnabelioid vertex).fiberFunctor
  letI : CategoryTheory.Epi (refinement.val.app vertex) := by
    change CategoryTheory.Epi ((SourceSemiGraphOfAnabelioids.GluedObject.evaluation
      (diagram := diagram) vertex).map refinement.val)
    infer_instance
  have surjective := CategoryTheory.PreGaloisCategory.surjective_on_fiber_of_epi
    (diagram.vertexAnabelioid vertex).fiber (refinement.val.app vertex)
  intro targetPoint
  obtain ⟨sourcePoint, maps⟩ := surjective targetPoint
  refine ⟨sourcePoint, ?_⟩
  exact (EtaleFundamentalGroup.finiteTemperification_map_apply
    (diagram.vertexAnabelioid vertex) (refinement.val.app vertex)
      sourcePoint).trans maps

/-- Refinement maps a lifted universal-cover vertex by mapping its reduced
incidence walk and its finite-level endpoint. -/
noncomputable def refinementLiftedVertex
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : SourceSemiGraphUniversalCover.LiftedVertex
      (LevelSemiGraph diagram root finer) finer.rootVertex) :
    SourceSemiGraphUniversalCover.LiftedVertex
      (LevelSemiGraph diagram root coarser) coarser.rootVertex where
  path := RefinementTreeMap diagram root refinement vertex.path
  vertex := (GaloisLevel.transition diagram root refinement).vertexMap
    vertex.vertex
  endpoint_eq := by
    rw [refinementTreeMap_endpoint, vertex.endpoint_eq]
    rfl

@[simp]
theorem refinementLiftedVertex_projection
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : SourceSemiGraphUniversalCover.LiftedVertex
      (LevelSemiGraph diagram root finer) finer.rootVertex) :
    coarser.projection.vertexMap
        (refinementLiftedVertex diagram root refinement vertex).vertex =
      finer.projection.vertexMap vertex.vertex :=
  GaloisLevel.transition_vertex_over_base diagram root refinement vertex.vertex

/-- Refinement restricted to the lifted vertices over one base vertex. -/
noncomputable def refinementVertexIndexMap
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : diagram.base.Vertex) :
    SourceFiniteLevelUniversalCover.VertexIndex diagram root finer.object
        finer.rootVertex vertex →
      SourceFiniteLevelUniversalCover.VertexIndex diagram root coarser.object
        coarser.rootVertex vertex :=
  fun index ↦ ⟨refinementLiftedVertex diagram root refinement index.1,
    (refinementLiftedVertex_projection
      diagram root refinement index.1).trans index.2⟩

/-- Every lifted vertex at a coarser level has a lifted preimage at a finer
level. -/
theorem refinementVertexIndexMap_surjective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : diagram.base.Vertex) :
    Function.Surjective
      (refinementVertexIndexMap diagram root refinement vertex) := by
  intro target
  obtain ⟨sourcePath, pathMaps⟩ :=
    refinementTreeMap_surjective diagram root refinement target.1.path
  have endpointMaps := congrArg (fun point ↦ point.endpoint) pathMaps
  change (RefinementTreeMap diagram root refinement sourcePath).endpoint =
    target.1.path.endpoint at endpointMaps
  rw [refinementTreeMap_endpoint, target.1.endpoint_eq] at endpointMaps
  cases endpointEquality : sourcePath.endpoint with
  | vertex compactVertex =>
      cases compactVertex with
      | inl sourceVertex =>
          let lifted : SourceSemiGraphUniversalCover.LiftedVertex
              (LevelSemiGraph diagram root finer) finer.rootVertex :=
            { path := sourcePath
              vertex := sourceVertex
              endpoint_eq := endpointEquality }
          have liftedMaps :
              refinementLiftedVertex diagram root refinement lifted =
                target.1 := by
            apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
            exact pathMaps
          have baseEquality : sourceVertex.1 = vertex := by
            rw [← target.2]
            have vertexMaps := congrArg
              SourceSemiGraphUniversalCover.LiftedVertex.vertex liftedMaps
            rw [← vertexMaps]
            exact GaloisLevel.transition_vertex_over_base
              diagram root refinement sourceVertex
          let sourceIndex : SourceFiniteLevelUniversalCover.VertexIndex
              diagram root finer.object finer.rootVertex vertex :=
            ⟨lifted, baseEquality⟩
          refine ⟨sourceIndex, ?_⟩
          apply Subtype.ext
          exact liftedMaps
      | inr boundary =>
          rw [endpointEquality] at endpointMaps
          simp [RefinementIncidenceMap] at endpointMaps
  | edge sourceEdge =>
      rw [endpointEquality] at endpointMaps
      simp [RefinementIncidenceMap] at endpointMaps
  | branch sourceBranch =>
      rw [endpointEquality] at endpointMaps
      simp [RefinementIncidenceMap] at endpointMaps

/-- The retained finite point map sends the component selected by a lifted
finer vertex to the component selected by its refined vertex. -/
theorem selectedVertexComponent_refinement
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : diagram.base.Vertex)
    (index : SourceFiniteLevelUniversalCover.VertexIndex diagram root
      finer.object finer.rootVertex vertex) :
    coverVertexComponentMap diagram (finiteCovMap diagram root refinement.val)
        vertex
        (SourceFiniteLevelUniversalCover.selectedVertexComponent
          diagram root finer.object finer.rootVertex vertex index) =
      SourceFiniteLevelUniversalCover.selectedVertexComponent
        diagram root coarser.object coarser.rootVertex vertex
        (refinementVertexIndexMap diagram root refinement vertex index) := by
  rcases index with ⟨lifted, baseEquality⟩
  subst vertex
  letI := (diagram.vertexAnabelioid lifted.vertex.1).coverCategory
  unfold SourceFiniteLevelUniversalCover.selectedVertexComponent
  rw [← finiteVertexComponentEquiv_naturality]
  rfl

/-- The constituent morphism on one base vertex. -/
noncomputable def refinementVertexHom
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (vertex : diagram.base.Vertex) :
    (SourceFiniteLevelUniversalCover.covObject
        diagram root finer.object finer.rootVertex).vertexObject vertex ⟶
      (SourceFiniteLevelUniversalCover.covObject
        diagram root coarser.object coarser.rootVertex).vertexObject vertex := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  let finiteMap :=
    (EtaleFundamentalGroup.coverActionEquivalence
      (diagram.vertexAnabelioid vertex)).functor.map
        (refinement.val.app vertex)
  exact SourceTemperoidComponentFamily.map finiteMap
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root finer.object finer.rootVertex vertex)
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root coarser.object coarser.rootVertex vertex)
    (refinementVertexIndexMap diagram root refinement vertex)
    (selectedVertexComponent_refinement diagram root refinement vertex)

@[simp]
theorem refinementVertexHom_apply_index
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (vertex : diagram.base.Vertex)
    (point : (SourceFiniteLevelUniversalCover.covObject
      diagram root finer.object finer.rootVertex).vertexObject vertex |>.obj.V.obj) :
    ((refinementVertexHom diagram root refinement vertex).hom.hom point).1 =
      refinementVertexIndexMap diagram root refinement vertex point.1 :=
  rfl

@[simp]
theorem refinementVertexHom_apply_value
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (vertex : diagram.base.Vertex)
    (point : (SourceFiniteLevelUniversalCover.covObject
      diagram root finer.object finer.rootVertex).vertexObject vertex |>.obj.V.obj) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    ((refinementVertexHom diagram root refinement vertex).hom.hom point).2.1 =
      (diagram.vertexAnabelioid vertex).fiber.map
        (refinement.val.app vertex) point.2.1 :=
  by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    rfl

/-- Refinement maps a lifted universal-cover edge by the same reduced-walk
map and the finite-level edge transition. -/
noncomputable def refinementLiftedEdge
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (edge : SourceSemiGraphUniversalCover.LiftedEdge
      (LevelSemiGraph diagram root finer) finer.rootVertex) :
    SourceSemiGraphUniversalCover.LiftedEdge
      (LevelSemiGraph diagram root coarser) coarser.rootVertex where
  path := RefinementTreeMap diagram root refinement edge.path
  edge := (GaloisLevel.transition diagram root refinement).edgeMap edge.edge
  endpoint_eq := by
    rw [refinementTreeMap_endpoint, edge.endpoint_eq]
    rfl

@[simp]
theorem refinementLiftedEdge_projection
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (edge : SourceSemiGraphUniversalCover.LiftedEdge
      (LevelSemiGraph diagram root finer) finer.rootVertex) :
    coarser.projection.edgeMap
        (refinementLiftedEdge diagram root refinement edge).edge =
      finer.projection.edgeMap edge.edge :=
  GaloisLevel.transition_edge_over_base diagram root refinement edge.edge

/-- Refinement restricted to lifted edges over one base edge. -/
noncomputable def refinementEdgeIndexMap
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (edge : diagram.base.Edge) :
    SourceFiniteLevelUniversalCover.EdgeIndex diagram root finer.object
        finer.rootVertex edge →
      SourceFiniteLevelUniversalCover.EdgeIndex diagram root coarser.object
        coarser.rootVertex edge :=
  fun index ↦ ⟨refinementLiftedEdge diagram root refinement index.1,
    (refinementLiftedEdge_projection
      diagram root refinement index.1).trans index.2⟩

/-- The retained finite edge point map respects the selected lifted-edge
components. -/
theorem selectedEdgeComponent_refinement
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (edge : diagram.base.Edge)
    (index : SourceFiniteLevelUniversalCover.EdgeIndex diagram root
      finer.object finer.rootVertex edge) :
    let reference :=
      SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    SourceSemiGraphOfAnabelioids.CovObject.actionComponentMap
        ((diagram.edgeAnabelioid edge).finiteTemperification.map
          (reference.pullback.map (refinement.val.app reference.vertex)))
        (SourceFiniteLevelUniversalCover.selectedEdgeComponent
          diagram root finer.object finer.rootVertex edge index) =
      SourceFiniteLevelUniversalCover.selectedEdgeComponent
        diagram root coarser.object coarser.rootVertex edge
        (refinementEdgeIndexMap diagram root refinement edge index) := by
  rcases index with ⟨lifted, rfl⟩
  let reference :=
    SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      diagram root lifted.edge.1
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid lifted.edge.1).coverCategory
  simpa only [SourceFiniteLevelUniversalCover.selectedEdgeComponent,
    refinementEdgeIndexMap, refinementLiftedEdge, GaloisLevel.transition,
    SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition,
    SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverEdgeMap,
    SourceSemiGraphOfAnabelioids.CovObject.finiteCanonicalEdgeComponentEquiv]
    using (EtaleFundamentalGroup.fiberComponentFiniteActionEquiv_naturality
      (diagram.edgeAnabelioid lifted.edge.1)
      (reference.pullback.map (refinement.val.app reference.vertex))
      lifted.edge.2).symm

/-- The constituent morphism on one base edge. -/
noncomputable def refinementEdgeHom
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (edge : diagram.base.Edge) :
    SourceFiniteLevelUniversalCover.edgeAction
        diagram root finer.object finer.rootVertex edge ⟶
      SourceFiniteLevelUniversalCover.edgeAction
        diagram root coarser.object coarser.rootVertex edge := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let reference :=
    SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  let finiteMap :=
    (EtaleFundamentalGroup.coverActionEquivalence
      (diagram.edgeAnabelioid edge)).functor.map
        (reference.pullback.map (refinement.val.app reference.vertex))
  exact SourceTemperoidComponentFamily.map finiteMap
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root finer.object finer.rootVertex edge)
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root coarser.object coarser.rootVertex edge)
    (refinementEdgeIndexMap diagram root refinement edge)
    (selectedEdgeComponent_refinement diagram root refinement edge)

@[simp]
theorem refinementEdgeHom_apply_index
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (edge : diagram.base.Edge)
    (point : (SourceFiniteLevelUniversalCover.edgeAction
      diagram root finer.object finer.rootVertex edge).obj.V.obj) :
    ((refinementEdgeHom diagram root refinement edge).hom.hom point).1 =
      refinementEdgeIndexMap diagram root refinement edge point.1 :=
  rfl

@[simp]
theorem refinementEdgeHom_apply_value
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (edge : diagram.base.Edge)
    (point : (SourceFiniteLevelUniversalCover.edgeAction
      diagram root finer.object finer.rootVertex edge).obj.V.obj) :
    let reference :=
      SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ((refinementEdgeHom diagram root refinement edge).hom.hom point).2.1 =
      (diagram.edgeAnabelioid edge).fiber.map
        (reference.pullback.map (refinement.val.app reference.vertex))
        point.2.1 := by
  let reference :=
    SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  rfl

/-- Refinement of the universal incidence tree preserves the unique edge
incident to a lifted vertex along a finite-level branch. -/
theorem refinementLiftedEdge_incidentEdge
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : SourceSemiGraphUniversalCover.LiftedVertex
      (LevelSemiGraph diagram root finer) finer.rootVertex)
    (branch : (LevelSemiGraph diagram root finer).IncidentBranch vertex.vertex) :
    refinementLiftedEdge diagram root refinement
        (SourceSemiGraphUniversalCover.incidentEdge
          (LevelSemiGraph diagram root finer) finer.rootVertex vertex branch) =
      SourceSemiGraphUniversalCover.incidentEdge
        (LevelSemiGraph diagram root coarser) coarser.rootVertex
        (refinementLiftedVertex diagram root refinement vertex)
        ((GaloisLevel.transition diagram root refinement).incidentBranchMap
          vertex.vertex branch) := by
  apply SourceSemiGraphUniversalCover.LiftedEdge.path_injective
  change RefinementTreeMap diagram root refinement
      (SourceSemiGraphUniversalCover.incidentEdge
        (LevelSemiGraph diagram root finer) finer.rootVertex vertex branch).path =
    (SourceSemiGraphUniversalCover.incidentEdge
      (LevelSemiGraph diagram root coarser) coarser.rootVertex
      (refinementLiftedVertex diagram root refinement vertex)
      ((GaloisLevel.transition diagram root refinement).incidentBranchMap
        vertex.vertex branch)).path
  let sourceBranchPath := SourceSemiGraphUniversalCover.incidentBranchPath
    (LevelSemiGraph diagram root finer) finer.rootVertex vertex branch
  let targetBranch :=
    (GaloisLevel.transition diagram root refinement).incidentBranchMap
      vertex.vertex branch
  let targetBranchPath := SourceSemiGraphUniversalCover.incidentBranchPath
    (LevelSemiGraph diagram root coarser) coarser.rootVertex
      (refinementLiftedVertex diagram root refinement vertex) targetBranch
  have branchPathEquality :
      RefinementTreeMap diagram root refinement sourceBranchPath =
        targetBranchPath := by
    apply UniversalVertex.neighbor_eq_of_endpoint_eq
      (IncidenceGraph diagram root coarser)
      (IncidenceRoot diagram root coarser)
    · exact refinementTreeMap_adj diagram root refinement
        (UniversalVertex.adjacent_liftNeighbor
          (IncidenceGraph diagram root finer)
          (IncidenceRoot diagram root finer) vertex.path
          (IncidenceNode.branch branch.1) _)
    · exact UniversalVertex.adjacent_liftNeighbor
        (IncidenceGraph diagram root coarser)
        (IncidenceRoot diagram root coarser)
        (refinementLiftedVertex diagram root refinement vertex).path
        (IncidenceNode.branch targetBranch.1) _
    · simp only [sourceBranchPath, targetBranchPath,
        SourceSemiGraphUniversalCover.incidentBranchPath,
        refinementTreeMap_endpoint,
        UniversalVertex.liftNeighbor_endpoint]
      rfl
  apply UniversalVertex.neighbor_eq_of_endpoint_eq
    (IncidenceGraph diagram root coarser)
    (IncidenceRoot diagram root coarser)
    (point := targetBranchPath)
  · rw [← branchPathEquality]
    exact refinementTreeMap_adj diagram root refinement
      (UniversalVertex.adjacent_liftNeighbor
        (IncidenceGraph diagram root finer)
        (IncidenceRoot diagram root finer) sourceBranchPath
        (IncidenceNode.edge branch.1.edge) _)
  · exact UniversalVertex.adjacent_liftNeighbor
      (IncidenceGraph diagram root coarser)
      (IncidenceRoot diagram root coarser) targetBranchPath
      (IncidenceNode.edge targetBranch.1.edge) _
  · simp only [SourceSemiGraphUniversalCover.incidentEdge,
      refinementTreeMap_endpoint,
      UniversalVertex.liftNeighbor_endpoint]
    rfl

/-- The retained point of a finer selected vertex component maps into the
component selected by the refined lifted vertex. -/
theorem refinementVertexPointComponent
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    ∀ (index : SourceFiniteLevelUniversalCover.VertexIndex diagram root
        finer.object finer.rootVertex vertex)
      (point : (diagram.vertexAnabelioid vertex).fiber.obj
        (finer.object.vertexObject vertex)),
      Quotient.mk'' point =
          SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root finer.object finer.rootVertex vertex index →
        Quotient.mk'' ((diagram.vertexAnabelioid vertex).fiber.map
            (refinement.val.app vertex) point) =
          SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root coarser.object coarser.rootVertex vertex
            (refinementVertexIndexMap diagram root refinement vertex index) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  intro index point pointComponent
  rw [← selectedVertexComponent_refinement
    diagram root refinement vertex index]
  unfold SourceSemiGraphOfAnabelioids.CovObject.coverVertexComponentMap
  rw [← pointComponent]
  rfl

/-- The finite branch comparison is natural in the underlying Galois-level
refinement, on the retained finite points. -/
theorem refinementFiniteBranchActionIso_hom_apply
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    let reference :=
      SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ (point : (diagram.vertexAnabelioid branch.vertex).fiber.obj
      (finer.object.vertexObject branch.vertex)),
    (diagram.edgeAnabelioid edge).fiber.map
        (reference.pullback.map (refinement.val.app reference.vertex))
        ((SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso
          diagram root finer.object branch).hom.hom.hom point) =
      (SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso
          diagram root coarser.object branch).hom.hom.hom
        ((diagram.vertexAnabelioid branch.vertex).fiber.map
          (refinement.val.app branch.vertex) point) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  dsimp only
  intro point
  have naturality :=
    SourceSemiGraphOfAnabelioids.CovObject.finiteEdgeIdentification_naturality
      diagram root refinement.val branch
  have underlyingEquality :=
    congrArg (fun morphism ↦ morphism.hom.hom) naturality
  have pointEquality :=
    CategoryTheory.ConcreteCategory.congr_hom underlyingEquality point
  simpa only [
    SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso_hom_apply,
    CategoryTheory.ObjectProperty.FullSubcategory.comp_hom,
    Action.comp_hom, SourceCountableTypeCat.comp_apply] using pointEquality

/-- The finite edge component represented by a retained branch point maps to
the corresponding coarser represented component. -/
theorem refinementRestrictedFiniteEdgeOfPoint
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    let reference :=
      SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ (index : SourceFiniteLevelUniversalCover.VertexIndex diagram root
        finer.object finer.rootVertex branch.vertex)
      (point : (diagram.vertexAnabelioid branch.vertex).fiber.obj
        (finer.object.vertexObject branch.vertex))
      (pointComponent : Quotient.mk'' point =
        SourceFiniteLevelUniversalCover.selectedVertexComponent
          diagram root finer.object finer.rootVertex branch.vertex index),
      (GaloisLevel.transition diagram root refinement).edgeMap
          ⟨edge, SourceFiniteLevelUniversalCover.restrictedFiniteEdgeComponent
            diagram root finer.object finer.rootVertex branch
            (restrictedBranchIndexOfPoint diagram root finer branch
              index point pointComponent)⟩ =
        ⟨edge, SourceFiniteLevelUniversalCover.restrictedFiniteEdgeComponent
          diagram root coarser.object coarser.rootVertex branch
          (restrictedBranchIndexOfPoint diagram root coarser branch
            (refinementVertexIndexMap diagram root refinement branch.vertex index)
            ((diagram.vertexAnabelioid branch.vertex).fiber.map
              (refinement.val.app branch.vertex) point)
            (refinementVertexPointComponent
              diagram root refinement branch.vertex index point pointComponent))⟩ := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  dsimp only
  intro index point pointComponent
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply (SourceSemiGraphOfAnabelioids.CovObject.finiteCanonicalEdgeComponentEquiv
      diagram root coarser.object edge).injective
    unfold SourceFiniteLevelUniversalCover.restrictedFiniteEdgeComponent
    rw [Equiv.apply_symm_apply]
    unfold GaloisLevel.transition
    unfold SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
      SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverEdgeMap
      SourceSemiGraphOfAnabelioids.CovObject.finiteCanonicalEdgeComponentEquiv
      SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
    change (diagram.edgeAnabelioid edge).fiberComponentFiniteActionEquiv
        (reference.pullback.obj
          (coarser.object.vertexObject reference.vertex))
        ((diagram.edgeAnabelioid edge).fiberComponentHomMap
          (reference.pullback.map (refinement.val.app reference.vertex))
          (((diagram.edgeAnabelioid edge).fiberComponentFiniteActionEquiv
            (reference.pullback.obj
              (finer.object.vertexObject reference.vertex))).symm
            ((sourceFiniteActionComponentEquiv
              (SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso
                diagram root finer.object branch))
              (restrictedBranchIndexOfPoint diagram root finer branch
                index point pointComponent).2.1))) = _
    rw [EtaleFundamentalGroup.fiberComponentFiniteActionEquiv_naturality]
    rw [Equiv.apply_symm_apply]
    unfold sourceFiniteActionComponentEquiv
    change Quotient.mk'' _ = Quotient.mk'' _
    exact congrArg Quotient.mk''
      (refinementFiniteBranchActionIso_hom_apply
        diagram root refinement branch point)

/-- The explicit vertex and edge refinement maps commute with the geometric
branch-to-edge comparison. -/
theorem refinementBranchEdgeFamilyIso_naturality
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    CategoryTheory.CategoryStruct.comp
        (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root finer.object finer.rootVertex branch).hom
        (refinementEdgeHom diagram root refinement edge) =
      CategoryTheory.CategoryStruct.comp
        (branch.temperoidPullback.map
          (refinementVertexHom diagram root refinement branch.vertex))
        (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root coarser.object coarser.rootVertex branch).hom := by
  let reference :=
    SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  apply CategoryTheory.ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro point
  rcases point with ⟨index, point⟩
  let sourceRestricted := restrictedBranchIndexOfPoint
    diagram root finer branch index point.1 point.2
  let targetPointComponent := refinementVertexPointComponent
    diagram root refinement branch.vertex index point.1 point.2
  let targetRestricted := restrictedBranchIndexOfPoint
    diagram root coarser branch
      (refinementVertexIndexMap diagram root refinement branch.vertex index)
      ((diagram.vertexAnabelioid branch.vertex).fiber.map
        (refinement.val.app branch.vertex) point.1)
      targetPointComponent
  let input :
      (branch.temperoidPullback.obj
        ((SourceFiniteLevelUniversalCover.covObject
          diagram root finer.object finer.rootVertex).vertexObject
            branch.vertex)).obj.V.obj :=
    ⟨index, point⟩
  let leftPoint :=
    (refinementEdgeHom diagram root refinement edge).hom.hom
      ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root finer.object finer.rootVertex branch).hom.hom.hom input)
  let rightPoint :=
    (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root coarser.object coarser.rootVertex branch).hom.hom.hom
        ((branch.temperoidPullback.map
          (refinementVertexHom diagram root refinement branch.vertex)).hom.hom
            input)
  change leftPoint = rightPoint
  have indexEquality : leftPoint.1 = rightPoint.1 := by
    dsimp only [leftPoint, rightPoint, input]
    unfold SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
    simp only [CategoryTheory.Iso.trans_hom,
      CategoryTheory.ObjectProperty.FullSubcategory.comp_hom,
      Action.comp_hom, CategoryTheory.ConcreteCategory.comp_apply]
    change refinementEdgeIndexMap diagram root refinement edge
        (SourceFiniteLevelUniversalCover.restrictedBranchIndexEquivEdgeIndex
          diagram root finer.object finer.rootVertex branch sourceRestricted) =
      SourceFiniteLevelUniversalCover.restrictedBranchIndexEquivEdgeIndex
        diagram root coarser.object coarser.rootVertex branch targetRestricted
    have finiteEdgeEquality := refinementRestrictedFiniteEdgeOfPoint
      diagram root refinement branch index point.1 point.2
    have finiteBranchEquality :
        (GaloisLevel.transition diagram root refinement).incidentBranchMap
            sourceRestricted.1.1.vertex
            (SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
              diagram root finer.object finer.rootVertex branch sourceRestricted) =
          SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
            diagram root coarser.object coarser.rootVertex branch
              targetRestricted := by
      apply Subtype.ext
      apply Sigma.ext
      · exact finiteEdgeEquality
      · rfl
    apply Subtype.ext
    change refinementLiftedEdge diagram root refinement
        (SourceSemiGraphUniversalCover.incidentEdge
          (LevelSemiGraph diagram root finer) finer.rootVertex
          sourceRestricted.1.1
          (SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
            diagram root finer.object finer.rootVertex branch
              sourceRestricted)) =
      SourceSemiGraphUniversalCover.incidentEdge
        (LevelSemiGraph diagram root coarser) coarser.rootVertex
        targetRestricted.1.1
        (SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
          diagram root coarser.object coarser.rootVertex branch
            targetRestricted)
    calc
      _ = SourceSemiGraphUniversalCover.incidentEdge
            (LevelSemiGraph diagram root coarser) coarser.rootVertex
            (refinementLiftedVertex diagram root refinement
              sourceRestricted.1.1)
            ((GaloisLevel.transition diagram root refinement).incidentBranchMap
              sourceRestricted.1.1.vertex
              (SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
                diagram root finer.object finer.rootVertex branch
                  sourceRestricted)) :=
        refinementLiftedEdge_incidentEdge diagram root refinement
          sourceRestricted.1.1 _
      _ = _ := by
        rw [finiteBranchEquality]
        rfl
  apply Sigma.ext indexEquality
  rw [Subtype.heq_iff_coe_heq rfl (by
    apply heq_of_eq
    funext value
    apply propext
    rw [indexEquality])]
  dsimp only [leftPoint, rightPoint, input]
  unfold SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
  simp only [CategoryTheory.Iso.trans_hom,
    CategoryTheory.ObjectProperty.FullSubcategory.comp_hom,
    Action.comp_hom]
  exact heq_of_eq
    (refinementFiniteBranchActionIso_hom_apply
      diagram root refinement branch point.1)

/-- The inverse branch comparison satisfies the equivalent refinement
naturality square. -/
theorem refinementBranchEdgeFamilyIso_inv_naturality
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    CategoryTheory.CategoryStruct.comp
        (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root finer.object finer.rootVertex branch).inv
        (branch.temperoidPullback.map
          (refinementVertexHom diagram root refinement branch.vertex)) =
      CategoryTheory.CategoryStruct.comp
        (refinementEdgeHom diagram root refinement edge)
        (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root coarser.object coarser.rootVertex branch).inv := by
  let sourceIso := SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
    diagram root finer.object finer.rootVertex branch
  let targetIso := SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
    diagram root coarser.object coarser.rootVertex branch
  let vertexMap := branch.temperoidPullback.map
    (refinementVertexHom diagram root refinement branch.vertex)
  let edgeMap := refinementEdgeHom diagram root refinement edge
  change CategoryTheory.CategoryStruct.comp sourceIso.inv vertexMap =
    CategoryTheory.CategoryStruct.comp edgeMap targetIso.inv
  apply (CategoryTheory.cancel_mono targetIso.hom).mp
  calc
    CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp sourceIso.inv vertexMap)
          targetIso.hom =
        CategoryTheory.CategoryStruct.comp sourceIso.inv
          (CategoryTheory.CategoryStruct.comp vertexMap targetIso.hom) :=
      CategoryTheory.Category.assoc _ _ _
    _ = CategoryTheory.CategoryStruct.comp sourceIso.inv
          (CategoryTheory.CategoryStruct.comp sourceIso.hom edgeMap) := by
      exact congrArg
        (fun map => CategoryTheory.CategoryStruct.comp sourceIso.inv map)
        (refinementBranchEdgeFamilyIso_naturality
          diagram root refinement branch).symm
    _ = edgeMap := sourceIso.inv_hom_id_assoc edgeMap
    _ = CategoryTheory.CategoryStruct.comp edgeMap
          (CategoryTheory.CategoryStruct.comp targetIso.inv targetIso.hom) := by
      simp

/-- The constituentwise refinement maps assemble to a literal morphism of
the geometric universal-cover objects. -/
noncomputable def explicitUniversalCoverRefinementHom
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    SourceFiniteLevelUniversalCover.covObject
        diagram root finer.object finer.rootVertex ⟶
      SourceFiniteLevelUniversalCover.covObject
        diagram root coarser.object coarser.rootVertex where
  app vertex := refinementVertexHom diagram root refinement vertex
  naturality := by
    intro edge first second
    let finerFirstIso := SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root finer.object finer.rootVertex first
    let finerSecondIso := SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root finer.object finer.rootVertex second
    let coarserFirstIso := SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root coarser.object coarser.rootVertex first
    let coarserSecondIso := SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root coarser.object coarser.rootVertex second
    let firstMap := first.temperoidPullback.map
      (refinementVertexHom diagram root refinement first.vertex)
    let secondMap := second.temperoidPullback.map
      (refinementVertexHom diagram root refinement second.vertex)
    let edgeMap := refinementEdgeHom diagram root refinement edge
    change CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp finerFirstIso.hom
          finerSecondIso.inv) secondMap =
      CategoryTheory.CategoryStruct.comp
        firstMap (CategoryTheory.CategoryStruct.comp
          coarserFirstIso.hom coarserSecondIso.inv)
    exact (CategoryTheory.Category.assoc
        finerFirstIso.hom finerSecondIso.inv secondMap).trans
      ((congrArg
        (fun map => CategoryTheory.CategoryStruct.comp finerFirstIso.hom map)
        (refinementBranchEdgeFamilyIso_inv_naturality
          diagram root refinement second)).trans
      ((CategoryTheory.Category.assoc
        finerFirstIso.hom edgeMap coarserSecondIso.inv).symm.trans
      ((congrArg
        (fun map => CategoryTheory.CategoryStruct.comp map coarserSecondIso.inv)
        (refinementBranchEdgeFamilyIso_naturality
          diagram root refinement first)).trans
        (CategoryTheory.Category.assoc
          firstMap coarserFirstIso.hom coarserSecondIso.inv))))

/-- The explicit refinement morphism preserves the distinguished geometric
root point. -/
theorem explicitUniversalCoverRefinementHom_root
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    ((explicitUniversalCoverRefinementHom
      diagram root refinement).app root).hom.hom
        (rootVertexPoint diagram root finer) =
      rootVertexPoint diagram root coarser := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  letI := (diagram.vertexAnabelioid root).coverCategory
  let sourcePoint := rootVertexPoint diagram root finer
  let targetPoint := rootVertexPoint diagram root coarser
  change (refinementVertexHom diagram root refinement root).hom.hom
      sourcePoint = targetPoint
  have indexEquality :
      ((refinementVertexHom diagram root refinement root).hom.hom
        sourcePoint).1 = targetPoint.1 := by
    apply Subtype.ext
    apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    change RefinementTreeMap diagram root refinement
        (UniversalVertex.base (IncidenceGraph diagram root finer)
          (IncidenceRoot diagram root finer)) =
      UniversalVertex.base (IncidenceGraph diagram root coarser)
        (IncidenceRoot diagram root coarser)
    exact refinementTreeMap_base diagram root refinement
  apply Sigma.ext indexEquality
  rw [Subtype.heq_iff_coe_heq rfl (by
    apply heq_of_eq
    funext value
    apply propext
    rw [indexEquality])]
  apply heq_of_eq
  change (diagram.vertexAnabelioid root).fiber.map
      (refinement.val.app root) finer.point = coarser.point
  exact refinement.comp

/-- The retained finite point map commutes with descent of complete deck
transformations along a Galois-level refinement. -/
theorem refinementDeckFinitePoint
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    ∀ point : (diagram.vertexAnabelioid vertex).fiber.obj
        (finer.object.vertexObject vertex),
      (diagram.vertexAnabelioid vertex).fiber.map
          (refinement.val.app vertex)
          ((deckVertexFiniteActionIso
            diagram root finer transformation vertex).hom.hom.hom point) =
        (deckVertexFiniteActionIso diagram root coarser
          (deckTransition diagram root refinement transformation)
          vertex).hom.hom.hom
            ((diagram.vertexAnabelioid vertex).fiber.map
              (refinement.val.app vertex) point) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI : CategoryTheory.GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : CategoryTheory.PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram vertex
  letI : CategoryTheory.PreGaloisCategory.IsGalois finer.object :=
    finer.isGalois
  letI : CategoryTheory.PreGaloisCategory.IsGalois coarser.object :=
    coarser.isGalois
  intro point
  let symmetry :=
    UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation
  change (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
      diagram vertex).map refinement.val
        ((SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
          diagram vertex).map symmetry.hom point) =
    (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
      diagram vertex).map
        (GaloisLevel.automorphismTransition
          diagram root refinement symmetry).hom
        ((SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
          diagram vertex).map refinement.val point)
  exact (CategoryTheory.PreGaloisCategory.comp_autMap_apply
    (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex)
    refinement.val symmetry point).symm

/-- Refinement of a lifted vertex commutes with the descended complete deck
transformation. -/
theorem refinementVertexIndexMap_deck
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer)
    (vertex : diagram.base.Vertex)
    (index : SourceFiniteLevelUniversalCover.VertexIndex
      diagram root finer.object finer.rootVertex vertex) :
    refinementVertexIndexMap diagram root refinement vertex
        (deckVertexIndexEquiv
          diagram root finer transformation vertex index) =
      deckVertexIndexEquiv diagram root coarser
        (deckTransition diagram root refinement transformation) vertex
        (refinementVertexIndexMap diagram root refinement vertex index) := by
  apply Subtype.ext
  apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
  exact deckTransitionToFun_commutes
    diagram root refinement transformation index.1.path

/-- The explicit constituent map intertwines the finite-level geometric
deck actions. -/
theorem refinementVertexHom_deck
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (vertex : diagram.base.Vertex) :
    CategoryTheory.CategoryStruct.comp
        (deckVertexActionIso
          diagram root finer transformation vertex).hom
        (refinementVertexHom diagram root refinement vertex) =
      CategoryTheory.CategoryStruct.comp
        (refinementVertexHom diagram root refinement vertex)
        (deckVertexActionIso diagram root coarser
          (deckTransition diagram root refinement transformation)
          vertex).hom := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  apply CategoryTheory.ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro point
  have indexEquality :
      (((refinementVertexHom diagram root refinement vertex).hom.hom
        ((deckVertexActionIso diagram root finer transformation
          vertex).hom.hom.hom point)).1) =
      (((deckVertexActionIso diagram root coarser
        (deckTransition diagram root refinement transformation)
        vertex).hom.hom.hom
          ((refinementVertexHom diagram root refinement vertex).hom.hom
            point)).1) := by
    exact refinementVertexIndexMap_deck
      diagram root refinement transformation vertex point.1
  apply Sigma.ext indexEquality
  rw [Subtype.heq_iff_coe_heq rfl (by
    apply heq_of_eq
    funext value
    apply propext
    rw [indexEquality])]
  exact heq_of_eq
    (refinementDeckFinitePoint
      diagram root refinement transformation vertex point.2.1)

/-- The explicit geometric refinement morphism is equivariant for the deck
group transition. -/
theorem explicitUniversalCoverRefinementHom_deck
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    CategoryTheory.CategoryStruct.comp
        (deckCovHom diagram root finer transformation)
        (explicitUniversalCoverRefinementHom
          diagram root refinement) =
      CategoryTheory.CategoryStruct.comp
        (explicitUniversalCoverRefinementHom diagram root refinement)
        (deckCovHom diagram root coarser
          (deckTransition diagram root refinement transformation)) := by
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  exact refinementVertexHom_deck
    diagram root refinement transformation vertex

/-- A surjective equivariant map makes the kernel of the source action a
subgroup of the kernel of the target action. -/
theorem actionKernelFixes_of_surjective_map
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {source target : SourceTemperoidAction G}
    (map : source ⟶ target)
    (surjective : Function.Surjective map.hom.hom) :
    SourceSemiGraphOfAnabelioids.CovObject.ActionKernelFixes source target := by
  intro element fixes targetPoint
  obtain ⟨sourcePoint, rfl⟩ := surjective targetPoint
  exact (CategoryTheory.ConcreteCategory.congr_hom
      (map.hom.comm element) sourcePoint).symm.trans
    (congrArg map.hom.hom (fixes sourcePoint))

/-- The representative edge map of a pointed Galois refinement is
surjective.  Restriction along an incident branch does not change its
underlying point map. -/
theorem refinementEdgeRestrictionMap_surjective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (edge : diagram.base.Edge) :
    let reference :=
      SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    Function.Surjective
      ((reference.temperoidPullback.map
        ((finiteCovMap diagram root refinement.val).app
          reference.vertex)).hom.hom) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  dsimp only
  intro targetPoint
  obtain ⟨sourcePoint, maps⟩ :=
    refinementVertexMap_surjective
      diagram root refinement reference.vertex targetPoint
  exact ⟨sourcePoint, maps⟩

/-- A finer pointed Galois level still splits the geometric universal cover
constructed at a coarser level. -/
theorem refinementSplitsUniversalCover
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    SourceSemiGraphOfAnabelioids.CovObject.IsSplitBy diagram root
      finer.object
      (SourceFiniteLevelUniversalCover.covObject
        diagram root coarser.object coarser.rootVertex) := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let coarserSplit := Iut.SourceFiniteLevelUniversalCover.covObject_isSplitBy
    diagram root coarser.object coarser.rootVertex
  constructor
  · intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (actionKernelFixes_of_surjective_map
      ((finiteCovMap diagram root refinement.val).app vertex)
      (refinementVertexMap_surjective
        diagram root refinement vertex)).trans (coarserSplit.1 vertex)
  · intro edge
    let reference :=
      SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    exact (actionKernelFixes_of_surjective_map
      (reference.temperoidPullback.map
        ((finiteCovMap diagram root refinement.val).app reference.vertex))
      (refinementEdgeRestrictionMap_surjective
        diagram root refinement edge)).trans (coarserSplit.2 edge)

/-- The normalization witness for the geometric refinement map: its selected
domination morphism sends the finer distinguished point to the coarser one. -/
noncomputable def refinementInitial
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    (SourceFiniteLevelUniversalCover.covObject
      diagram root coarser.object coarser.rootVertex).vertexObject root
        |>.obj.V.obj :=
  Classical.choose
    (SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.exists_geometricDomination_maps_root
      diagram root finer
        (SourceFiniteLevelUniversalCover.covObject
          diagram root coarser.object coarser.rootVertex)
        (refinementSplitsUniversalCover diagram root refinement)
        (rootVertexPoint diagram root coarser))

/-- The canonical pointed morphism between the literal geometric universal
covers attached to two refined Galois levels. -/
noncomputable def universalCoverRefinementHom
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    SourceFiniteLevelUniversalCover.covObject
        diagram root finer.object finer.rootVertex ⟶
      SourceFiniteLevelUniversalCover.covObject
        diagram root coarser.object coarser.rootVertex := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  exact SourceSemiGraphOfAnabelioids.CovObject.GeometricDomination.hom
    diagram root finer
    (SourceFiniteLevelUniversalCover.covObject
      diagram root coarser.object coarser.rootVertex)
    (refinementSplitsUniversalCover diagram root refinement)
    (refinementInitial diagram root refinement)

/-- The refinement morphism preserves the distinguished geometric root
point by construction. -/
theorem universalCoverRefinementHom_root
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    ((universalCoverRefinementHom diagram root refinement).app root).hom.hom
        (rootVertexPoint diagram root finer) =
      rootVertexPoint diagram root coarser :=
  Classical.choose_spec
    (SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.exists_geometricDomination_maps_root
      diagram root finer
        (SourceFiniteLevelUniversalCover.covObject
          diagram root coarser.object coarser.rootVertex)
        (refinementSplitsUniversalCover diagram root refinement)
        (rootVertexPoint diagram root coarser))

/-- Pointed uniqueness identifies the geometric-domination refinement with
the explicit constituentwise refinement morphism. -/
theorem universalCoverRefinementHom_eq_explicit
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    universalCoverRefinementHom diagram root refinement =
      explicitUniversalCoverRefinementHom diagram root refinement := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  apply SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.hom_ext_of_isPointConnected
      (⟨root, rootVertexPoint diagram root finer⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.GeometricPoint
          (SourceFiniteLevelUniversalCover.covObject
            diagram root finer.object finer.rootVertex))
      (covObject_isPointConnected diagram root finer)
  rw [universalCoverRefinementHom_root,
    explicitUniversalCoverRefinementHom_root]

/-- The canonical pointed geometric refinement morphism is equivariant for
the deck transition. -/
theorem universalCoverRefinementHom_deck
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    CategoryTheory.CategoryStruct.comp
        (deckCovHom diagram root finer transformation)
        (universalCoverRefinementHom diagram root refinement) =
      CategoryTheory.CategoryStruct.comp
        (universalCoverRefinementHom diagram root refinement)
        (deckCovHom diagram root coarser
          (deckTransition diagram root refinement transformation)) := by
  rw [universalCoverRefinementHom_eq_explicit
    diagram root refinement]
  exact explicitUniversalCoverRefinementHom_deck
    diagram root refinement transformation

/-- A finite deck-group transition bundled with its canonical continuity
between discrete deck groups. -/
noncomputable def continuousDeckTransition
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    DeckGroup diagram root finer →ₜ* DeckGroup diagram root coarser where
  toMonoidHom := deckTransition diagram root refinement
  continuous_toFun := continuous_of_discreteTopology

/-- Restrict a coarser finite-level action along a pointed deck-group
refinement. -/
noncomputable def restrictDeckAction
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (object : SourceTemperoidAction (DeckGroup diagram root coarser)) :
    SourceTemperoidAction (DeckGroup diagram root finer) :=
  (ContAction.res SourceCountableTypeCat
    (continuousDeckTransition diagram root refinement)).obj object

/-- Pointwise form of deck equivariance for the geometric universal-cover
refinement. -/
theorem universalCoverRefinementHom_smul
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (vertex : diagram.base.Vertex)
    (point : (SourceFiniteLevelUniversalCover.covObject
      diagram root finer.object finer.rootVertex).vertexObject vertex
        |>.obj.V.obj) :
    ((universalCoverRefinementHom diagram root refinement).app vertex).hom.hom
        ((deckVertexActionIso
          diagram root finer transformation vertex).hom.hom.hom point) =
      (deckVertexActionIso diagram root coarser
        (deckTransition diagram root refinement transformation) vertex).hom.hom.hom
        (((universalCoverRefinementHom diagram root refinement).app vertex).hom.hom
          point) := by
  exact CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun arrow ↦ (arrow.app vertex).hom.hom)
      (universalCoverRefinementHom_deck
        diagram root refinement transformation)) point

/-- Refining the universal cover and restricting the auxiliary action induces
the canonical map between the two finite-level associated quotients. -/
noncomputable def associatedTemperedRefinementHom
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (object : SourceTemperoidAction (DeckGroup diagram root coarser)) :
    (associatedTemperedFunctor diagram root finer).obj
        (restrictDeckAction diagram root refinement object) ⟶
      (associatedTemperedFunctor diagram root coarser).obj object := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  apply CategoryTheory.ObjectProperty.homMk
  exact SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.sourceMapOfTransition
    (SourceFiniteLevelUniversalCover.covObject
      diagram root finer.object finer.rootVertex)
    (deckCovActionHom diagram root finer)
    (SourceFiniteLevelUniversalCover.covObject
      diagram root coarser.object coarser.rootVertex)
    (deckCovActionHom diagram root coarser)
    (deckTransition diagram root refinement)
    (universalCoverRefinementHom diagram root refinement)
    (fun transformation ↦
      universalCoverRefinementHom_deck
        diagram root refinement transformation)
    object

/-- The change-of-level map on associated quotients is bijective on every
constituent.  Surjectivity lifts the geometric source point.  Injectivity
uses transitivity upstairs and freeness downstairs to show that the required
correction lies in the kernel of the deck transition. -/
theorem associatedTemperedRefinementHom_app_bijective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (object : SourceTemperoidAction (DeckGroup diagram root coarser))
    (vertex : diagram.base.Vertex) :
    Function.Bijective
      (((associatedTemperedRefinementHom
        diagram root refinement object).hom.app vertex).hom.hom) := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let finerSource := SourceFiniteLevelUniversalCover.covObject
    diagram root finer.object finer.rootVertex
  let coarserSource := SourceFiniteLevelUniversalCover.covObject
    diagram root coarser.object coarser.rootVertex
  let finerDeckAction := deckCovActionHom diagram root finer
  let coarserDeckAction := deckCovActionHom diagram root coarser
  let transition := deckTransition diagram root refinement
  let sourceMap := universalCoverRefinementHom diagram root refinement
  letI : MulAction (DeckGroup diagram root finer) object.obj.V.obj :=
    MulAction.compHom object.obj.V.obj transition
  letI : MulAction (DeckGroup diagram root coarser)
      (restrictDeckAction diagram root refinement object).obj.V.obj := by
    change MulAction (DeckGroup diagram root coarser) object.obj.V.obj
    infer_instance
  letI finerSourceAction :=
    SourceTemperoidAssociatedQuotient.sourceDeckMulAction
      (finerSource.vertexObject vertex)
      (vertexDeckAction finerSource finerDeckAction vertex)
  letI coarserSourceAction :=
    SourceTemperoidAssociatedQuotient.sourceDeckMulAction
      (coarserSource.vertexObject vertex)
      (vertexDeckAction coarserSource coarserDeckAction vertex)
  constructor
  · intro first second equality
    induction first using Quotient.inductionOn' with
    | _ first =>
      induction second using Quotient.inductionOn' with
      | _ second =>
        change SourceTemperoidAssociatedQuotient.mk
            (coarserSource.vertexObject vertex)
            (vertexDeckAction coarserSource coarserDeckAction vertex)
            ((sourceMap.app vertex).hom.hom first.1,
              (first.2 : object.obj.V.obj)) =
          SourceTemperoidAssociatedQuotient.mk
            (coarserSource.vertexObject vertex)
            (vertexDeckAction coarserSource coarserDeckAction vertex)
            ((sourceMap.app vertex).hom.hom second.1,
              (second.2 : object.obj.V.obj)) at equality
        have related := Quotient.exact equality
        change ((sourceMap.app vertex).hom.hom first.1, first.2) ∈
          MulAction.orbit (DeckGroup diagram root coarser)
            ((sourceMap.app vertex).hom.hom second.1, second.2) at related
        obtain ⟨coarserTransformation, orbitEquality⟩ :=
          MulAction.mem_orbit_iff.mp related
        obtain ⟨finerTransformation, transformationMaps⟩ :=
          deckTransition_surjective diagram root refinement
            coarserTransformation
        obtain ⟨correction, correctionMaps⟩ :=
          (vertexDeckAction_isPretransitive
            diagram root finer vertex).exists_smul_eq
              (finerTransformation • second.1) first.1
        have mappedLiftedPoint :
            (sourceMap.app vertex).hom.hom
                (finerTransformation • second.1) =
              coarserTransformation •
                (sourceMap.app vertex).hom.hom second.1 := by
          change (sourceMap.app vertex).hom.hom
              ((deckVertexActionIso diagram root finer
                finerTransformation vertex).hom.hom.hom second.1) =
            (deckVertexActionIso diagram root coarser coarserTransformation
              vertex).hom.hom.hom ((sourceMap.app vertex).hom.hom second.1)
          exact (universalCoverRefinementHom_smul diagram root refinement
            finerTransformation vertex second.1).trans <| congrArg
              (fun transformation : DeckGroup diagram root coarser ↦
                (deckVertexActionIso diagram root coarser transformation
                  vertex).hom.hom.hom
                    ((sourceMap.app vertex).hom.hom second.1))
              transformationMaps
        have coarserPointEquality :
            coarserTransformation •
                (sourceMap.app vertex).hom.hom second.1 =
              (sourceMap.app vertex).hom.hom first.1 :=
          congrArg Prod.fst orbitEquality
        have correctionImageFixes :
            transition correction •
                (sourceMap.app vertex).hom.hom first.1 =
              (sourceMap.app vertex).hom.hom first.1 := by
          calc
            transition correction •
                (sourceMap.app vertex).hom.hom first.1 =
              transition correction •
                (sourceMap.app vertex).hom.hom
                  (finerTransformation • second.1) := by
                    rw [mappedLiftedPoint, coarserPointEquality]
            _ = (sourceMap.app vertex).hom.hom
                  (correction • (finerTransformation • second.1)) := by
                    change (deckVertexActionIso diagram root coarser
                        (transition correction) vertex).hom.hom.hom
                          ((sourceMap.app vertex).hom.hom
                            (finerTransformation • second.1)) =
                      (sourceMap.app vertex).hom.hom
                        ((deckVertexActionIso diagram root finer correction
                          vertex).hom.hom.hom
                            (finerTransformation • second.1))
                    exact (universalCoverRefinementHom_smul diagram root
                      refinement correction vertex
                        (finerTransformation • second.1)).symm
            _ = (sourceMap.app vertex).hom.hom first.1 :=
              congrArg (sourceMap.app vertex).hom.hom correctionMaps
        letI : IsCancelSMul (DeckGroup diagram root coarser)
            (coarserSource.vertexObject vertex).obj.V.obj :=
          vertexDeckAction_isCancel diagram root coarser vertex
        have correctionImageOne : transition correction = 1 :=
          IsCancelSMul.eq_one_of_smul correctionImageFixes
        apply Quotient.sound
        change first ∈ MulAction.orbit (DeckGroup diagram root finer) second
        refine MulAction.mem_orbit_iff.mpr
          ⟨correction * finerTransformation, ?_⟩
        apply Prod.ext
        · simpa only [mul_smul] using correctionMaps
        · have auxiliaryEquality := congrArg Prod.snd orbitEquality
          change coarserTransformation • second.2 = first.2 at auxiliaryEquality
          change transition (correction * finerTransformation) • second.2 = first.2
          rw [map_mul, correctionImageOne, one_mul, transformationMaps]
          exact auxiliaryEquality
  · intro targetPoint
    induction targetPoint using Quotient.inductionOn' with
    | _ targetPoint =>
      obtain ⟨sourceIndex, indexMaps⟩ :=
        refinementVertexIndexMap_surjective
          diagram root refinement vertex targetPoint.1.1
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      let finiteMap :=
        (EtaleFundamentalGroup.coverActionEquivalence
          (diagram.vertexAnabelioid vertex)).functor.map
            (refinement.val.app vertex)
      let sourceComponent :=
        SourceFiniteLevelUniversalCover.selectedVertexComponent
          diagram root finer.object finer.rootVertex vertex sourceIndex
      let targetComponent :=
        SourceFiniteLevelUniversalCover.selectedVertexComponent
          diagram root coarser.object coarser.rootVertex vertex targetPoint.1.1
      let sourceBase := sourceComponent.out
      have sourceBaseComponent : Quotient.mk'' sourceBase = sourceComponent :=
        Quotient.out_eq' sourceComponent
      have mappedBaseComponent :
          Quotient.mk'' (finiteMap.hom.hom sourceBase) = targetComponent := by
        have atRefinedIndex := refinementVertexPointComponent
          diagram root refinement vertex sourceIndex sourceBase
            sourceBaseComponent
        change Quotient.mk'' (finiteMap.hom.hom sourceBase) =
          SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root coarser.object coarser.rootVertex vertex
              (refinementVertexIndexMap
                diagram root refinement vertex sourceIndex) at atRefinedIndex
        exact atRefinedIndex.trans <| congrArg
          (SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root coarser.object coarser.rootVertex vertex) indexMaps
      have sameOrbitClass : Quotient.mk'' targetPoint.1.2.1 =
          Quotient.mk'' (finiteMap.hom.hom sourceBase) :=
        targetPoint.1.2.2.trans mappedBaseComponent.symm
      have sameOrbit := Quotient.exact sameOrbitClass
      change targetPoint.1.2.1 ∈ MulAction.orbit
        (diagram.vertexAnabelioid vertex).group
          (finiteMap.hom.hom sourceBase) at sameOrbit
      obtain ⟨localTransformation, localMaps⟩ :=
        MulAction.mem_orbit_iff.mp sameOrbit
      have sourcePointComponent :
          Quotient.mk'' (localTransformation • sourceBase) =
            sourceComponent := by
        calc
          Quotient.mk'' (localTransformation • sourceBase) =
              Quotient.mk'' sourceBase := by
            apply Quotient.sound
            change localTransformation • sourceBase ∈ MulAction.orbit
              (diagram.vertexAnabelioid vertex).group sourceBase
            exact MulAction.mem_orbit _ localTransformation
          _ = sourceComponent := sourceBaseComponent
      have finitePointMaps :
          finiteMap.hom.hom (localTransformation • sourceBase) =
            targetPoint.1.2.1 := by
        calc
          finiteMap.hom.hom (localTransformation • sourceBase) =
              localTransformation • finiteMap.hom.hom sourceBase :=
            CategoryTheory.ConcreteCategory.congr_hom
              (finiteMap.hom.comm localTransformation) sourceBase
          _ = targetPoint.1.2.1 := localMaps
      let sourceGeometricPoint :
          (finerSource.vertexObject vertex).obj.V.obj :=
        ⟨sourceIndex,
          ⟨localTransformation • sourceBase, sourcePointComponent⟩⟩
      have sourceGeometricPointMaps :
          (sourceMap.app vertex).hom.hom sourceGeometricPoint = targetPoint.1 := by
        change ((universalCoverRefinementHom
          diagram root refinement).app vertex).hom.hom
            sourceGeometricPoint = targetPoint.1
        rw [universalCoverRefinementHom_eq_explicit]
        have geometricIndexMaps :
            (((explicitUniversalCoverRefinementHom
              diagram root refinement).app vertex).hom.hom
                sourceGeometricPoint).1 = targetPoint.1.1 := by
          change refinementVertexIndexMap
            diagram root refinement vertex sourceIndex = targetPoint.1.1
          exact indexMaps
        apply Sigma.ext geometricIndexMaps
        rw [Subtype.heq_iff_coe_heq rfl (by
          apply heq_of_eq
          funext value
          apply propext
          rw [geometricIndexMaps])]
        exact heq_of_eq finitePointMaps
      refine ⟨SourceTemperoidAssociatedQuotient.mk
        (finerSource.vertexObject vertex)
        (vertexDeckAction finerSource finerDeckAction vertex)
        (sourceGeometricPoint, targetPoint.2), ?_⟩
      change SourceTemperoidAssociatedQuotient.mk
          (coarserSource.vertexObject vertex)
          (vertexDeckAction coarserSource coarserDeckAction vertex)
          ((sourceMap.app vertex).hom.hom sourceGeometricPoint,
            targetPoint.2) =
        SourceTemperoidAssociatedQuotient.mk
          (coarserSource.vertexObject vertex)
          (vertexDeckAction coarserSource coarserDeckAction vertex)
          targetPoint
      exact congrArg
        (SourceTemperoidAssociatedQuotient.mk
          (coarserSource.vertexObject vertex)
          (vertexDeckAction coarserSource coarserDeckAction vertex))
        (Prod.ext sourceGeometricPointMaps rfl)

/-- Associated quotients are canonically unchanged after refining the
universal cover and restricting the auxiliary deck action. -/
noncomputable def associatedTemperedRefinementIso
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (object : SourceTemperoidAction (DeckGroup diagram root coarser)) :
    (associatedTemperedFunctor diagram root finer).obj
        (restrictDeckAction diagram root refinement object) ≅
      (associatedTemperedFunctor diagram root coarser).obj object := by
  apply CategoryTheory.ObjectProperty.isoMk
  exact covObjectIsoOfComponentwiseBijective
    (associatedTemperedRefinementHom diagram root refinement object).hom
    (associatedTemperedRefinementHom_app_bijective
      diagram root refinement object)

@[simp]
theorem associatedTemperedRefinementIso_hom
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (object : SourceTemperoidAction (DeckGroup diagram root coarser)) :
    (associatedTemperedRefinementIso
      diagram root refinement object).hom =
      associatedTemperedRefinementHom diagram root refinement object :=
  rfl

/-- At the distinguished root, the associated-quotient refinement map keeps
the auxiliary value and sends the finer universal-cover base point to the
coarser one. -/
@[simp]
theorem associatedTemperedRefinementHom_root_mk
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (object : SourceTemperoidAction (DeckGroup diagram root coarser))
    (point : object.obj.V.obj) :
    (((associatedTemperedRefinementHom
      diagram root refinement object).hom.app root).hom.hom)
        (rootAssociatedCarrierEquiv diagram root finer
          (restrictDeckAction diagram root refinement object) point) =
      rootAssociatedCarrierEquiv diagram root coarser object point := by
  rw [rootAssociatedCarrierEquiv_apply, rootAssociatedCarrierEquiv_apply]
  change SourceTemperoidAssociatedQuotient.mk
      ((SourceFiniteLevelUniversalCover.covObject
        diagram root coarser.object coarser.rootVertex).vertexObject root)
      (vertexDeckAction
        (SourceFiniteLevelUniversalCover.covObject
          diagram root coarser.object coarser.rootVertex)
        (deckCovActionHom diagram root coarser) root)
      (((universalCoverRefinementHom
        diagram root refinement).app root).hom.hom
          (rootVertexPoint diagram root finer), point) = _
  rw [universalCoverRefinementHom_root]

/-- The inverse refinement isomorphism sends a coarser normalized root class
back to the finer normalized root class with the same auxiliary value. -/
@[simp]
theorem associatedTemperedRefinementIso_inv_root_mk
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (object : SourceTemperoidAction (DeckGroup diagram root coarser))
    (point : object.obj.V.obj) :
    (((associatedTemperedRefinementIso
      diagram root refinement object).inv.hom.app root).hom.hom)
        (rootAssociatedCarrierEquiv
          diagram root coarser object point) =
      rootAssociatedCarrierEquiv diagram root finer
        (restrictDeckAction diagram root refinement object) point := by
  apply (associatedTemperedRefinementHom_app_bijective
    diagram root refinement object root).1
  change ((CategoryTheory.CategoryStruct.comp
      (associatedTemperedRefinementIso
        diagram root refinement object).inv
      (associatedTemperedRefinementIso
        diagram root refinement object).hom).hom.app root).hom.hom _ = _
  rw [(associatedTemperedRefinementIso
    diagram root refinement object).inv_hom_id]
  exact (associatedTemperedRefinementHom_root_mk
    diagram root refinement object point).symm

/-- Pointed uniqueness makes the geometric map attached to the identity
refinement the identity morphism. -/
@[simp]
theorem universalCoverRefinementHom_id
    (level : GaloisLevel diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    universalCoverRefinementHom diagram root
        (CategoryTheory.CategoryStruct.id level) =
      CategoryTheory.CategoryStruct.id
        (SourceFiniteLevelUniversalCover.covObject
          diagram root level.object level.rootVertex) := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  apply SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.hom_ext_of_isPointConnected
      (⟨root, rootVertexPoint diagram root level⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.GeometricPoint
          (SourceFiniteLevelUniversalCover.covObject
            diagram root level.object level.rootVertex))
      (covObject_isPointConnected diagram root level)
  exact universalCoverRefinementHom_root
    diagram root (CategoryTheory.CategoryStruct.id level)

/-- Pointed uniqueness also makes refinement morphisms strictly compatible
with composition. -/
theorem universalCoverRefinementHom_comp
    {first middle last : GaloisLevel diagram root}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    universalCoverRefinementHom diagram root
        (CategoryTheory.CategoryStruct.comp firstMap secondMap) =
      CategoryTheory.CategoryStruct.comp
        (universalCoverRefinementHom diagram root firstMap)
        (universalCoverRefinementHom diagram root secondMap) := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  apply SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.hom_ext_of_isPointConnected
      (⟨root, rootVertexPoint diagram root first⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.GeometricPoint
          (SourceFiniteLevelUniversalCover.covObject
            diagram root first.object first.rootVertex))
      (covObject_isPointConnected diagram root first)
  change
    ((universalCoverRefinementHom diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap)).app root).hom.hom
        (rootVertexPoint diagram root first) =
      ((universalCoverRefinementHom diagram root secondMap).app root).hom.hom
        (((universalCoverRefinementHom diagram root firstMap).app root).hom.hom
          (rootVertexPoint diagram root first))
  rw [universalCoverRefinementHom_root,
    universalCoverRefinementHom_root,
    universalCoverRefinementHom_root]

/-- The literal geometric universal covers and their normalized refinement
morphisms form the cofiltered system used in the passage to the limit in
Proposition 3.6(ii). -/
noncomputable def geometricUniversalCoverFunctor
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    CategoryTheory.Functor (GaloisLevel diagram root) diagram.CovObject where
  obj level := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  map refinement := universalCoverRefinementHom diagram root refinement
  map_id level := universalCoverRefinementHom_id diagram root level
  map_comp firstMap secondMap :=
    universalCoverRefinementHom_comp diagram root firstMap secondMap

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
