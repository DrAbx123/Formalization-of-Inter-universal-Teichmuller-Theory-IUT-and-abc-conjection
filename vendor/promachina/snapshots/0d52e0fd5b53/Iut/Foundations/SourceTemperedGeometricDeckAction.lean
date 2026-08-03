/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedUniversalCoverDeckAction

/-!
# Geometric deck action on universal-cover constituents

This file lifts the component-level deck action to the literal constituent
actions of the geometric universal cover used in Proposition 3.6(ii).
-/

namespace Iut

universe u

open CategoryTheory
open SourceCombinatorialUniversalCover
open SourceSemiGraphOfAnabelioids.GluedObject
open SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

noncomputable section

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)

/-- A complete deck transformation commutes with the canonical lift of a
neighbor in the finite-level incidence graph. -/
theorem deckTreePerm_liftNeighbor
    (transformation : DeckGroup diagram root level)
    (point : IncidenceTreeVertex diagram root level)
    (target : IncidenceNode (LevelSemiGraph diagram root level))
    (adjacent : (IncidenceGraph diagram root level).Adj point.endpoint target) :
    UniversalVertex.CompositeDeckTransformation.treePerm transformation
        (UniversalVertex.liftNeighbor
          (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
          point target adjacent) =
      UniversalVertex.liftNeighbor
        (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
        (UniversalVertex.CompositeDeckTransformation.treePerm
          transformation point)
        (((IncidenceActionHom diagram root level)
          (UniversalVertex.CompositeDeckTransformation.baseSymmetry
            transformation)).val target)
        (by
          rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply]
          exact ((IncidenceActionHom diagram root level)
            (UniversalVertex.CompositeDeckTransformation.baseSymmetry
              transformation)).property point.endpoint target |>.mpr adjacent) := by
  apply UniversalVertex.neighbor_eq_of_endpoint_eq
    (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
  · exact (UniversalVertex.CompositeDeckTransformation.adjacency_apply_iff
      transformation point
        (UniversalVertex.liftNeighbor
          (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
          point target adjacent)).mpr
      (UniversalVertex.adjacent_liftNeighbor
        (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
        point target adjacent)
  · exact UniversalVertex.adjacent_liftNeighbor
      (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
      (UniversalVertex.CompositeDeckTransformation.treePerm
        transformation point)
      (((IncidenceActionHom diagram root level)
        (UniversalVertex.CompositeDeckTransformation.baseSymmetry
          transformation)).val target) _
  · rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply,
      UniversalVertex.liftNeighbor_endpoint,
      UniversalVertex.liftNeighbor_endpoint]

/-- The finite Galois action transports an incident finite-level branch to
an incident branch at the transformed finite-level vertex. -/
noncomputable def deckFiniteIncidentBranch
    (transformation : DeckGroup diagram root level)
    {vertex : (LevelSemiGraph diagram root level).Vertex}
    (branch : (LevelSemiGraph diagram root level).IncidentBranch vertex) :
    (LevelSemiGraph diagram root level).IncidentBranch
      (level.automorphismAction.vertexAction
        (UniversalVertex.CompositeDeckTransformation.baseSymmetry
          transformation) vertex) := by
  let symmetry :=
    UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation
  refine ⟨level.automorphismAction.branchAction symmetry branch.1, ?_⟩
  have equivariance := level.automorphismAction.coincidence_action
    symmetry branch.1
  rw [branch.2] at equivariance
  exact equivariance

/-- The complete deck action carries the unique lifted edge incident to a
lifted vertex and finite branch to the unique lifted edge at the transformed
vertex and branch. -/
theorem deckEdgeMap_incidentEdge
    (transformation : DeckGroup diagram root level)
    (vertex : (Cover diagram root level).Vertex)
    (branch : (LevelSemiGraph diagram root level).IncidentBranch
      vertex.vertex) :
    deckEdgeMap diagram root level transformation
        (SourceSemiGraphUniversalCover.incidentEdge
          (LevelSemiGraph diagram root level) level.rootVertex vertex branch) =
      SourceSemiGraphUniversalCover.incidentEdge
        (LevelSemiGraph diagram root level) level.rootVertex
        (deckVertexMap diagram root level transformation vertex)
        (deckFiniteIncidentBranch
          diagram root level transformation branch) := by
  apply SourceSemiGraphUniversalCover.LiftedEdge.path_injective
  change UniversalVertex.CompositeDeckTransformation.treePerm transformation
      (UniversalVertex.liftNeighbor _ _
        (SourceSemiGraphUniversalCover.incidentBranchPath
          (LevelSemiGraph diagram root level) level.rootVertex vertex branch)
        (IncidenceNode.edge branch.1.edge) _) =
    UniversalVertex.liftNeighbor _ _
      (SourceSemiGraphUniversalCover.incidentBranchPath
        (LevelSemiGraph diagram root level) level.rootVertex
        (deckVertexMap diagram root level transformation vertex)
        (deckFiniteIncidentBranch
          diagram root level transformation branch))
      (IncidenceNode.edge
        (deckFiniteIncidentBranch
          diagram root level transformation branch).1.edge) _
  have branchPathEquality :
      UniversalVertex.CompositeDeckTransformation.treePerm transformation
          (SourceSemiGraphUniversalCover.incidentBranchPath
            (LevelSemiGraph diagram root level) level.rootVertex vertex branch) =
        SourceSemiGraphUniversalCover.incidentBranchPath
          (LevelSemiGraph diagram root level) level.rootVertex
          (deckVertexMap diagram root level transformation vertex)
          (deckFiniteIncidentBranch
            diagram root level transformation branch) := by
    unfold SourceSemiGraphUniversalCover.incidentBranchPath
    rw [deckTreePerm_liftNeighbor]
    rfl
  rw [deckTreePerm_liftNeighbor]
  apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
  · rw [branchPathEquality]
    exact UniversalVertex.adjacent_liftNeighbor _ _ _ _ _
  · rw [UniversalVertex.liftNeighbor_endpoint]
    rfl

/-- Indices of the realized universal-cover constituent over one source
vertex. -/
abbrev GeometricVertexIndex (vertex : diagram.base.Vertex) :=
  SourceFiniteLevelUniversalCover.VertexIndex diagram root level.object
    level.rootVertex vertex

/-- The component-level deck action restricts to an equivalence of the
indices lying over a fixed source vertex. -/
noncomputable def deckVertexIndexEquiv
    (transformation : DeckGroup diagram root level)
    (vertex : diagram.base.Vertex) :
    GeometricVertexIndex diagram root level vertex ≃
      GeometricVertexIndex diagram root level vertex where
  toFun index := ⟨deckVertexMap diagram root level transformation index.1,
    (deckVertexMap_projection diagram root level transformation index.1).trans
      index.2⟩
  invFun index := ⟨deckVertexMap diagram root level transformation⁻¹ index.1,
    (deckVertexMap_projection diagram root level transformation⁻¹
      index.1).trans index.2⟩
  left_inv index := by
    apply Subtype.ext
    apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    exact (UniversalVertex.CompositeDeckTransformation.treePerm
      transformation).symm_apply_apply index.1.path
  right_inv index := by
    apply Subtype.ext
    apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    exact (UniversalVertex.CompositeDeckTransformation.treePerm
      transformation).apply_symm_apply index.1.path

/-- The retained finite Galois symmetry induces an isomorphism of the finite
constituent action at every source vertex. -/
noncomputable def deckVertexFiniteActionIso
    (transformation : DeckGroup diagram root level)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    data.finiteAction (level.object.vertexObject vertex) ≅
      data.finiteAction (level.object.vertexObject vertex) := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  let symmetry :=
    UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation
  exact (EtaleFundamentalGroup.coverActionEquivalence data).functor.mapIso
    ((SourceSemiGraphOfAnabelioids.GluedObject.evaluation
      (diagram := diagram) vertex).mapIso
      symmetry)

/-- Reindexing by a deck transformation carries each selected finite orbit
component to the component selected at the transformed lifted vertex. -/
theorem deckVertexComponentCompatibility
    (transformation : DeckGroup diagram root level)
    (vertex : diagram.base.Vertex)
    (index : GeometricVertexIndex diagram root level vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    sourceFiniteActionComponentEquiv
        (deckVertexFiniteActionIso diagram root level transformation vertex)
        (SourceFiniteLevelUniversalCover.selectedVertexComponent
          diagram root level.object level.rootVertex vertex index) =
      SourceFiniteLevelUniversalCover.selectedVertexComponent
        diagram root level.object level.rootVertex vertex
          (deckVertexIndexEquiv
            diagram root level transformation vertex index) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  rcases index with
    ⟨⟨path, ⟨baseVertex, component⟩, endpointEquality⟩, baseEquality⟩
  change baseVertex = vertex at baseEquality
  cases baseEquality
  induction component using Quotient.inductionOn' with
  | _ point =>
      unfold SourceFiniteLevelUniversalCover.selectedVertexComponent
      unfold sourceFiniteActionComponentEquiv
      change Quotient.mk'' _ = Quotient.mk'' _
      rfl

/-- A complete deck transformation acts on the literal geometric vertex
constituent over every source vertex.  It simultaneously reindexes the
lifted component copy and applies the retained finite Galois symmetry inside
that copy. -/
noncomputable def deckVertexActionIso
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level)
    (vertex : diagram.base.Vertex) :
    SourceFiniteLevelUniversalCover.vertexAction
        diagram root level.object level.rootVertex vertex ≅
      SourceFiniteLevelUniversalCover.vertexAction
        diagram root level.object level.rootVertex vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact sourceTemperoidComponentFamilyActionIso
    (deckVertexFiniteActionIso diagram root level transformation vertex)
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root level.object level.rootVertex vertex)
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root level.object level.rootVertex vertex)
    (deckVertexIndexEquiv diagram root level transformation vertex)
    (deckVertexComponentCompatibility
      diagram root level transformation vertex)

/-- On the family index, the geometric vertex action is exactly the lifted
deck action. -/
@[simp]
theorem deckVertexActionIso_hom_apply_fst
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level)
    (vertex : diagram.base.Vertex)
    (point : SourceTemperoidComponentFamilyCarrier
      (diagram.vertexAnabelioid vertex).group
      ((diagram.vertexAnabelioid vertex).finiteAction
        (level.object.vertexObject vertex))
      (GeometricVertexIndex diagram root level vertex)
      (SourceFiniteLevelUniversalCover.selectedVertexComponent
        diagram root level.object level.rootVertex vertex)) :
    ((deckVertexActionIso diagram root level transformation vertex).hom.hom.hom
      point).1 =
        deckVertexIndexEquiv diagram root level transformation vertex point.1 :=
  rfl

/-- Inside each copied component, the geometric vertex action is exactly the
finite Galois symmetry retained by the complete deck transformation. -/
@[simp]
theorem deckVertexActionIso_hom_apply_val
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level)
    (vertex : diagram.base.Vertex)
    (point : SourceTemperoidComponentFamilyCarrier
      (diagram.vertexAnabelioid vertex).group
      ((diagram.vertexAnabelioid vertex).finiteAction
        (level.object.vertexObject vertex))
      (GeometricVertexIndex diagram root level vertex)
      (SourceFiniteLevelUniversalCover.selectedVertexComponent
        diagram root level.object level.rootVertex vertex)) :
    ((deckVertexActionIso diagram root level transformation vertex).hom.hom.hom
      point).2.1 =
        (deckVertexFiniteActionIso
          diagram root level transformation vertex).hom.hom.hom point.2.1 :=
  rfl

/-- Indices of the realized universal-cover edge constituent over one source
edge. -/
abbrev GeometricEdgeIndex (edge : diagram.base.Edge) :=
  SourceFiniteLevelUniversalCover.EdgeIndex diagram root level.object
    level.rootVertex edge

/-- The component-level deck action restricts to an equivalence of the
indices lying over a fixed source edge. -/
noncomputable def deckEdgeIndexEquiv
    (transformation : DeckGroup diagram root level)
    (edge : diagram.base.Edge) :
    GeometricEdgeIndex diagram root level edge ≃
      GeometricEdgeIndex diagram root level edge where
  toFun index := ⟨deckEdgeMap diagram root level transformation index.1,
    (deckEdgeMap_projection diagram root level transformation index.1).trans
      index.2⟩
  invFun index := ⟨deckEdgeMap diagram root level transformation⁻¹ index.1,
    (deckEdgeMap_projection diagram root level transformation⁻¹
      index.1).trans index.2⟩
  left_inv index := by
    apply Subtype.ext
    apply SourceSemiGraphUniversalCover.LiftedEdge.path_injective
    exact (UniversalVertex.CompositeDeckTransformation.treePerm
      transformation).symm_apply_apply index.1.path
  right_inv index := by
    apply Subtype.ext
    apply SourceSemiGraphUniversalCover.LiftedEdge.path_injective
    exact (UniversalVertex.CompositeDeckTransformation.treePerm
      transformation).apply_symm_apply index.1.path

/-- The retained finite Galois symmetry induces an isomorphism of the
canonical finite edge action at every source edge. -/
noncomputable def deckEdgeFiniteActionIso
    (transformation : DeckGroup diagram root level)
    (edge : diagram.base.Edge) :
    let reference :=
      SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (diagram.edgeAnabelioid edge).finiteAction
        (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
          diagram root level.object edge) ≅
      (diagram.edgeAnabelioid edge).finiteAction
        (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
          diagram root level.object edge) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  let symmetry :=
    UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation
  exact (EtaleFundamentalGroup.coverActionEquivalence
      (diagram.edgeAnabelioid edge)).functor.mapIso
    (reference.pullback.mapIso
      ((SourceSemiGraphOfAnabelioids.GluedObject.evaluation
        (diagram := diagram) reference.vertex).mapIso symmetry))

/-- The finite vertex and edge symmetries commute with the canonical finite
branch comparison.  This is the finite glued-object naturality square that
will control the point coordinate of the geometric gluing square. -/
theorem deckFiniteBranchActionIso_hom_apply
    (transformation : DeckGroup diagram root level)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    let reference :=
      SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ (point : (diagram.vertexAnabelioid branch.vertex).fiber.obj
      (level.object.vertexObject branch.vertex)),
    (deckEdgeFiniteActionIso
        diagram root level transformation edge).hom.hom.hom
      ((SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso
        diagram root level.object branch).hom.hom.hom point) =
    (SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso
        diagram root level.object branch).hom.hom.hom
      ((deckVertexFiniteActionIso
        diagram root level transformation branch.vertex).hom.hom.hom point) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  dsimp only
  intro point
  let symmetry :=
    UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation
  have naturality :=
    SourceSemiGraphOfAnabelioids.CovObject.finiteEdgeIdentification_naturality
      diagram root symmetry.hom branch
  have underlyingEquality :=
    congrArg (fun morphism ↦ morphism.hom.hom) naturality
  have pointEquality := ConcreteCategory.congr_hom underlyingEquality point
  simpa only [deckEdgeFiniteActionIso, deckVertexFiniteActionIso,
    SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso_hom_apply,
    ObjectProperty.FullSubcategory.comp_hom, Action.comp_hom,
    SourceCountableTypeCat.comp_apply] using pointEquality

/-- Reindexing by a deck transformation carries each selected finite edge
orbit to the orbit selected at the transformed lifted edge. -/
theorem deckEdgeComponentCompatibility
    (transformation : DeckGroup diagram root level)
    (edge : diagram.base.Edge)
    (index : GeometricEdgeIndex diagram root level edge) :
    let reference :=
      SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    sourceFiniteActionComponentEquiv
        (deckEdgeFiniteActionIso diagram root level transformation edge)
        (SourceFiniteLevelUniversalCover.selectedEdgeComponent
          diagram root level.object level.rootVertex edge index) =
      SourceFiniteLevelUniversalCover.selectedEdgeComponent
        diagram root level.object level.rootVertex edge
          (deckEdgeIndexEquiv
            diagram root level transformation edge index) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  rcases index with
    ⟨⟨path, ⟨baseEdge, component⟩, endpointEquality⟩, baseEquality⟩
  change baseEdge = edge at baseEquality
  cases baseEquality
  induction component using Quotient.inductionOn' with
  | _ point =>
      unfold SourceFiniteLevelUniversalCover.selectedEdgeComponent
      unfold sourceFiniteActionComponentEquiv
      change Quotient.mk'' _ = Quotient.mk'' _
      rfl

/-- A complete deck transformation acts on the common literal geometric
edge constituent over every source edge. -/
noncomputable def deckEdgeActionIso
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level)
    (edge : diagram.base.Edge) :
    SourceFiniteLevelUniversalCover.edgeAction
        diagram root level.object level.rootVertex edge ≅
      SourceFiniteLevelUniversalCover.edgeAction
        diagram root level.object level.rootVertex edge := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact sourceTemperoidComponentFamilyActionIso
    (deckEdgeFiniteActionIso diagram root level transformation edge)
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root level.object level.rootVertex edge)
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root level.object level.rootVertex edge)
    (deckEdgeIndexEquiv diagram root level transformation edge)
    (deckEdgeComponentCompatibility
      diagram root level transformation edge)

/-- On the edge-family index, the geometric action is exactly the lifted
deck action. -/
@[simp]
theorem deckEdgeActionIso_hom_apply_fst
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level)
    (edge : diagram.base.Edge)
    (point : SourceTemperoidComponentFamilyCarrier
      (diagram.edgeAnabelioid edge).group
      ((diagram.edgeAnabelioid edge).finiteAction
        (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
          diagram root level.object edge))
      (GeometricEdgeIndex diagram root level edge)
      (SourceFiniteLevelUniversalCover.selectedEdgeComponent
        diagram root level.object level.rootVertex edge)) :
    ((deckEdgeActionIso diagram root level transformation edge).hom.hom.hom
      point).1 =
        deckEdgeIndexEquiv diagram root level transformation edge point.1 :=
  rfl

/-- Inside each copied edge component, the action is the finite symmetry
induced on the chosen edge fiber. -/
@[simp]
theorem deckEdgeActionIso_hom_apply_val
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level)
    (edge : diagram.base.Edge)
    (point : SourceTemperoidComponentFamilyCarrier
      (diagram.edgeAnabelioid edge).group
      ((diagram.edgeAnabelioid edge).finiteAction
        (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
          diagram root level.object edge))
      (GeometricEdgeIndex diagram root level edge)
      (SourceFiniteLevelUniversalCover.selectedEdgeComponent
        diagram root level.object level.rootVertex edge)) :
    ((deckEdgeActionIso diagram root level transformation edge).hom.hom.hom
      point).2.1 =
        (deckEdgeFiniteActionIso
          diagram root level transformation edge).hom.hom.hom point.2.1 :=
  rfl

/-- Encode a point of a selected geometric vertex component as the refined
restricted-component index at an incident branch. -/
noncomputable def restrictedBranchIndexOfPoint
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    ∀ (index : GeometricVertexIndex diagram root level branch.vertex)
      (point : (diagram.vertexAnabelioid branch.vertex).fiber.obj
        (level.object.vertexObject branch.vertex)),
      Quotient.mk'' point =
          SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root level.object level.rootVertex branch.vertex index →
        SourceFiniteLevelUniversalCover.RestrictedBranchIndex
          diagram root level.object level.rootVertex branch := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  intro index point pointComponent
  exact ⟨index, ⟨Quotient.mk'' point,
    (sourceFiniteRestrictionComponentMap_mk
      (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
      ((diagram.vertexAnabelioid branch.vertex).finiteAction
        (level.object.vertexObject branch.vertex)) point).trans
      pointComponent⟩⟩

/-- The finite point action carries membership in a selected lifted vertex
component to membership in the transformed selected component. -/
theorem deckVertexPointComponent
    (transformation : DeckGroup diagram root level)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    ∀ (index : GeometricVertexIndex diagram root level vertex)
      (point : (diagram.vertexAnabelioid vertex).fiber.obj
        (level.object.vertexObject vertex)),
      Quotient.mk'' point =
          SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root level.object level.rootVertex vertex index →
        Quotient.mk''
            ((deckVertexFiniteActionIso
              diagram root level transformation vertex).hom.hom.hom point) =
          SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root level.object level.rootVertex vertex
            (deckVertexIndexEquiv
              diagram root level transformation vertex index) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  intro index point pointComponent
  rw [← deckVertexComponentCompatibility
    diagram root level transformation vertex index]
  unfold sourceFiniteActionComponentEquiv
  rw [← pointComponent]
  rfl

/-- The finite edge selected by a represented restricted branch component is
transported by the same finite Galois symmetry used in the complete deck
action. -/
theorem deckRestrictedFiniteEdgeOfPoint
    (transformation : DeckGroup diagram root level)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    let reference :=
      SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ (index : GeometricVertexIndex diagram root level branch.vertex)
      (point : (diagram.vertexAnabelioid branch.vertex).fiber.obj
        (level.object.vertexObject branch.vertex))
      (pointComponent : Quotient.mk'' point =
        SourceFiniteLevelUniversalCover.selectedVertexComponent
          diagram root level.object level.rootVertex branch.vertex index),
      level.automorphismAction.edgeAction
          (UniversalVertex.CompositeDeckTransformation.baseSymmetry
            transformation)
          ⟨edge, SourceFiniteLevelUniversalCover.restrictedFiniteEdgeComponent
            diagram root level.object level.rootVertex branch
            (restrictedBranchIndexOfPoint diagram root level branch
              index point pointComponent)⟩ =
        ⟨edge, SourceFiniteLevelUniversalCover.restrictedFiniteEdgeComponent
          diagram root level.object level.rootVertex branch
          (restrictedBranchIndexOfPoint diagram root level branch
            (deckVertexIndexEquiv
              diagram root level transformation branch.vertex index)
            ((deckVertexFiniteActionIso
              diagram root level transformation branch.vertex).hom.hom.hom
                point)
            (deckVertexPointComponent
              diagram root level transformation branch.vertex
                index point pointComponent))⟩ := by
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
      diagram root level.object edge).injective
    let symmetry :=
      UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation
    change (SourceSemiGraphOfAnabelioids.CovObject.finiteCanonicalEdgeComponentEquiv
        diagram root level.object edge)
        (EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.edgeAnabelioid edge)
          (reference.pullback.map (symmetry.hom.app reference.vertex))
          ((SourceSemiGraphOfAnabelioids.CovObject.finiteCanonicalEdgeComponentEquiv
            diagram root level.object edge).symm
            (Quotient.mk''
              ((SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso
                diagram root level.object branch).hom.hom.hom point)))) =
      Quotient.mk''
        ((SourceSemiGraphOfAnabelioids.CovObject.finiteBranchActionIso
          diagram root level.object branch).hom.hom.hom
          ((deckVertexFiniteActionIso
            diagram root level transformation branch.vertex).hom.hom.hom
              point))
    unfold SourceSemiGraphOfAnabelioids.CovObject.finiteCanonicalEdgeComponentEquiv
    rw [EtaleFundamentalGroup.fiberComponentFiniteActionEquiv_naturality]
    exact congrArg Quotient.mk''
      (deckFiniteBranchActionIso_hom_apply
        diagram root level transformation branch point)

/-- The geometric deck actions on vertex and edge constituents commute with
the canonical branch-to-edge comparison. -/
theorem deckBranchEdgeFamilyIso_naturality
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root level.object level.rootVertex branch).hom ≫
        (deckEdgeActionIso diagram root level transformation edge).hom =
      branch.temperoidPullback.map
          (deckVertexActionIso
            diagram root level transformation branch.vertex).hom ≫
        (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex branch).hom := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  change (deckEdgeActionIso diagram root level transformation edge).hom.hom.hom
      ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root level.object level.rootVertex branch).hom.hom.hom point) =
    (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root level.object level.rootVertex branch).hom.hom.hom
      ((deckVertexActionIso diagram root level transformation
        branch.vertex).hom.hom.hom point)
  let originalIndex := restrictedBranchIndexOfPoint
    diagram root level branch point.1 point.2.1 point.2.2
  let transformedPointComponent := deckVertexPointComponent
    diagram root level transformation branch.vertex
      point.1 point.2.1 point.2.2
  let transformedIndex := restrictedBranchIndexOfPoint
    diagram root level branch
      (deckVertexIndexEquiv
        diagram root level transformation branch.vertex point.1)
      ((deckVertexFiniteActionIso
        diagram root level transformation branch.vertex).hom.hom.hom
          point.2.1)
      transformedPointComponent
  have indexEquality :
      ((deckEdgeActionIso
        diagram root level transformation edge).hom.hom.hom
        ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex branch).hom.hom.hom
            point)).1 =
      ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root level.object level.rootVertex branch).hom.hom.hom
        ((deckVertexActionIso diagram root level transformation
          branch.vertex).hom.hom.hom point)).1 := by
    change deckEdgeIndexEquiv diagram root level transformation edge
        (SourceFiniteLevelUniversalCover.restrictedBranchIndexEquivEdgeIndex
          diagram root level.object level.rootVertex branch originalIndex) =
      SourceFiniteLevelUniversalCover.restrictedBranchIndexEquivEdgeIndex
        diagram root level.object level.rootVertex branch transformedIndex
    have finiteEdgeEquality := deckRestrictedFiniteEdgeOfPoint
      diagram root level transformation branch
        point.1 point.2.1 point.2.2
    have finiteBranchEquality :
        deckFiniteIncidentBranch diagram root level transformation
            (SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
              diagram root level.object level.rootVertex branch originalIndex) =
          SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
            diagram root level.object level.rootVertex branch
              transformedIndex := by
      apply Subtype.ext
      apply Sigma.ext
      · exact finiteEdgeEquality
      · rfl
    apply Subtype.ext
    change deckEdgeMap diagram root level transformation
        (SourceSemiGraphUniversalCover.incidentEdge
          (LevelSemiGraph diagram root level) level.rootVertex
          originalIndex.1.1
          (SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
            diagram root level.object level.rootVertex branch originalIndex)) =
      SourceSemiGraphUniversalCover.incidentEdge
        (LevelSemiGraph diagram root level) level.rootVertex
        transformedIndex.1.1
        (SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
          diagram root level.object level.rootVertex branch transformedIndex)
    calc
      _ = SourceSemiGraphUniversalCover.incidentEdge
            (LevelSemiGraph diagram root level) level.rootVertex
            (deckVertexMap diagram root level transformation originalIndex.1.1)
            (deckFiniteIncidentBranch diagram root level transformation
              (SourceFiniteLevelUniversalCover.restrictedFiniteIncidentBranch
                diagram root level.object level.rootVertex branch
                  originalIndex)) :=
        deckEdgeMap_incidentEdge
          diagram root level transformation originalIndex.1.1 _
      _ = _ := by
        rw [finiteBranchEquality]
        rfl
  apply Sigma.ext indexEquality
  rw [Subtype.heq_iff_coe_heq rfl (by
    apply heq_of_eq
    funext value
    apply propext
    rw [indexEquality])]
  exact heq_of_eq (deckFiniteBranchActionIso_hom_apply
    diagram root level transformation branch point.2.1)

/-- The inverse branch comparison satisfies the equivalent naturality
square. -/
theorem deckBranchEdgeFamilyIso_inv_naturality
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root level.object level.rootVertex branch).inv ≫
        branch.temperoidPullback.map
          (deckVertexActionIso
            diagram root level transformation branch.vertex).hom =
      (deckEdgeActionIso diagram root level transformation edge).hom ≫
        (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex branch).inv := by
  rw [← cancel_mono
    (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root level.object level.rootVertex branch).hom]
  rw [Category.assoc,
    ← deckBranchEdgeFamilyIso_naturality
      diagram root level transformation branch]
  simp

/-- Every complete deck transformation defines a genuine endomorphism of
the geometric universal-cover object; branch gluing is preserved by the
preceding naturality square. -/
noncomputable def deckCovHom
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level) :
    SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex ⟶
      SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex where
  app vertex := (deckVertexActionIso
    diagram root level transformation vertex).hom
  naturality := by
    intro edge first second
    change ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex first).hom ≫
        (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex second).inv) ≫
        second.temperoidPullback.map
          (deckVertexActionIso
            diagram root level transformation second.vertex).hom =
      first.temperoidPullback.map
          (deckVertexActionIso
            diagram root level transformation first.vertex).hom ≫
        ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex first).hom ≫
        (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex second).inv)
    rw [Category.assoc,
      deckBranchEdgeFamilyIso_inv_naturality
        diagram root level transformation second,
      ← Category.assoc,
      deckBranchEdgeFamilyIso_naturality
        diagram root level transformation first,
      Category.assoc]

/-- The identity complete deck transformation induces the identity
endomorphism of the geometric universal cover. -/
@[simp]
theorem deckCovHom_one
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    deckCovHom diagram root level 1 =
      𝟙 (SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex) := by
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  have indexEquality :
      (((deckCovHom diagram root level 1).app vertex).hom.hom point).1 =
        point.1 := by
    apply Subtype.ext
    apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    rfl
  apply Sigma.ext indexEquality
  rw [Subtype.heq_iff_coe_heq rfl (by
    apply heq_of_eq
    funext value
    apply propext
    rw [indexEquality])]
  apply heq_of_eq
  change (deckVertexFiniteActionIso
    diagram root level 1 vertex).hom.hom.hom point.2.1 = point.2.1
  have symmetryOne :
      UniversalVertex.CompositeDeckTransformation.baseSymmetry
          (1 : DeckGroup diagram root level) = 1 := rfl
  simp only [deckVertexFiniteActionIso, Functor.mapIso_hom]
  rw [symmetryOne]
  have oneHom : (1 : Aut level.object).hom = 𝟙 level.object := rfl
  rw [oneHom]
  rw [(SourceSemiGraphOfAnabelioids.GluedObject.evaluation
    (diagram := diagram) vertex).map_id]
  have mapIdentity :=
    (EtaleFundamentalGroup.coverActionEquivalence
      (diagram.vertexAnabelioid vertex)).functor.map_id
        ((SourceSemiGraphOfAnabelioids.GluedObject.evaluation
          (diagram := diagram) vertex).obj level.object)
  exact ConcreteCategory.congr_hom
    (congrArg (fun morphism ↦ morphism.hom.hom) mapIdentity) point.2.1

/-- Multiplication of complete deck transformations is carried to
composition of their geometric cover endomorphisms.  The order on the
right is the categorical convention for multiplication in `Aut`. -/
theorem deckCovHom_mul
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (first second : DeckGroup diagram root level) :
    deckCovHom diagram root level (first * second) =
      deckCovHom diagram root level second ≫
        deckCovHom diagram root level first := by
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  have indexEquality :
      (((deckCovHom diagram root level (first * second)).app vertex).hom.hom
          point).1 =
        (((deckCovHom diagram root level second ≫
          deckCovHom diagram root level first).app vertex).hom.hom point).1 := by
    apply Subtype.ext
    apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    rfl
  apply Sigma.ext indexEquality
  rw [Subtype.heq_iff_coe_heq rfl (by
    apply heq_of_eq
    funext value
    apply propext
    rw [indexEquality])]
  apply heq_of_eq
  change (deckVertexFiniteActionIso
      diagram root level (first * second) vertex).hom.hom.hom point.2.1 =
    (deckVertexFiniteActionIso
      diagram root level first vertex).hom.hom.hom
        ((deckVertexFiniteActionIso
          diagram root level second vertex).hom.hom.hom point.2.1)
  have symmetryMul :
      UniversalVertex.CompositeDeckTransformation.baseSymmetry
          (first * second) =
        UniversalVertex.CompositeDeckTransformation.baseSymmetry first *
          UniversalVertex.CompositeDeckTransformation.baseSymmetry second := rfl
  simp only [deckVertexFiniteActionIso, Functor.mapIso_hom]
  rw [symmetryMul, Aut.Aut_mul_def]
  rw [Iso.trans_hom]
  rw [(SourceSemiGraphOfAnabelioids.GluedObject.evaluation
    (diagram := diagram) vertex).map_comp]
  have mapComposition :=
    (EtaleFundamentalGroup.coverActionEquivalence
      (diagram.vertexAnabelioid vertex)).functor.map_comp
        ((SourceSemiGraphOfAnabelioids.GluedObject.evaluation
          (diagram := diagram) vertex).map
            (UniversalVertex.CompositeDeckTransformation.baseSymmetry
              second).hom)
        ((SourceSemiGraphOfAnabelioids.GluedObject.evaluation
          (diagram := diagram) vertex).map
            (UniversalVertex.CompositeDeckTransformation.baseSymmetry
              first).hom)
  exact ConcreteCategory.congr_hom
    (congrArg (fun morphism ↦ morphism.hom.hom) mapComposition) point.2.1

/-- Every complete deck transformation is an automorphism of the literal
geometric universal-cover object. -/
noncomputable def deckCovAut
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level) :
    Aut (SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex) where
  hom := deckCovHom diagram root level transformation
  inv := deckCovHom diagram root level transformation⁻¹
  hom_inv_id := by
    rw [← deckCovHom_mul diagram root level transformation⁻¹ transformation]
    simp
  inv_hom_id := by
    rw [← deckCovHom_mul diagram root level transformation transformation⁻¹]
    simp

@[simp]
theorem deckCovAut_hom
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level) :
    (deckCovAut diagram root level transformation).hom =
      deckCovHom diagram root level transformation :=
  rfl

@[simp]
theorem deckCovAut_inv
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level) :
    (deckCovAut diagram root level transformation).inv =
      deckCovHom diagram root level transformation⁻¹ :=
  rfl

/-- The complete finite-level deck group acts by genuine automorphisms of
the geometric universal-cover object. -/
noncomputable def deckCovActionHom
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    DeckGroup diagram root level →*
      Aut (SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex) where
  toFun := deckCovAut diagram root level
  map_one' := by
    apply Aut.ext
    exact deckCovHom_one diagram root level
  map_mul' first second := by
    apply Aut.ext
    rw [Aut.Aut_mul_def]
    exact deckCovHom_mul diagram root level first second

@[simp]
theorem deckCovActionHom_apply
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (transformation : DeckGroup diagram root level) :
    deckCovActionHom diagram root level transformation =
      deckCovAut diagram root level transformation :=
  rfl

end

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
