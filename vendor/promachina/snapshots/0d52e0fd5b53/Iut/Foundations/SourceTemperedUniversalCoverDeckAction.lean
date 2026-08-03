/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceCombinatorialUniversalCover
import Iut.Foundations.SourceTemperedGraphCoverRealization

/-!
# Deck orbits of geometric universal-cover levels

This file begins the connected quotient classification in *Semi-graphs of
Anabelioids*, Proposition 3.6(ii).  The complete finite-level deck group acts
on the vertices and edges of the universal semigraph cover.  The action uses
both pieces retained by `DeckGroup`: its lifted permutation of the universal
incidence tree and its finite Galois symmetry.

The main orbit theorems identify deck orbits exactly with fibers over the
source semigraph.  This is the component-level quotient statement used next
to construct the corresponding action on the literal geometric cover.
-/

universe u

open Iut
open Iut.SourceCombinatorialUniversalCover
open Iut.SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel

namespace Iut.SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

noncomputable section

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)

/-- A complete deck transformation sends a lifted vertex to the lift obtained
by applying its tree permutation and retained finite Galois symmetry. -/
noncomputable def deckVertexMap
    (transformation : DeckGroup diagram root level)
    (point : (Cover diagram root level).Vertex) :
    (Cover diagram root level).Vertex where
  path := UniversalVertex.CompositeDeckTransformation.treePerm transformation
    point.path
  vertex := (level.automorphismAction.vertexAction
    (UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation))
      point.vertex
  endpoint_eq := by
    rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply]
    rw [point.endpoint_eq]
    rfl

/-- A complete deck transformation sends a lifted edge to the lift obtained
by applying its tree permutation and retained finite Galois symmetry. -/
noncomputable def deckEdgeMap
    (transformation : DeckGroup diagram root level)
    (point : (Cover diagram root level).Edge) :
    (Cover diagram root level).Edge where
  path := UniversalVertex.CompositeDeckTransformation.treePerm transformation
    point.path
  edge := (level.automorphismAction.edgeAction
    (UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation))
      point.edge
  endpoint_eq := by
    rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply]
    rw [point.endpoint_eq]
    rfl

/-- The lifted-vertex maps form the complete deck-group action. -/
@[reducible]
noncomputable def deckVertexMulAction :
    MulAction (DeckGroup diagram root level)
      (Cover diagram root level).Vertex where
  smul := deckVertexMap diagram root level
  one_smul point := by
    apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    rfl
  mul_smul first second point := by
    apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    rfl

/-- The lifted-edge maps form the complete deck-group action. -/
@[reducible]
noncomputable def deckEdgeMulAction :
    MulAction (DeckGroup diagram root level)
      (Cover diagram root level).Edge where
  smul := deckEdgeMap diagram root level
  one_smul point := by
    apply SourceSemiGraphUniversalCover.LiftedEdge.path_injective
    rfl
  mul_smul first second point := by
    apply SourceSemiGraphUniversalCover.LiftedEdge.path_injective
    rfl

/-- Deck transformations preserve the projection of a lifted vertex to the
source semigraph. -/
theorem deckVertexMap_projection
    (transformation : DeckGroup diagram root level)
    (point : (Cover diagram root level).Vertex) :
    level.projection.vertexMap
        (deckVertexMap diagram root level transformation point).vertex =
      level.projection.vertexMap point.vertex := by
  have equality := baseIncidenceProjection_incidencePerm
    diagram root level
      (UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation)
      (IncidenceNode.vertex (Sum.inl point.vertex))
  rw [IncidenceNode.incidencePerm_vertex] at equality
  have compactVertexEquality :
      IncidenceNode.compactVertexPerm (LevelSemiGraph diagram root level)
          level.automorphismAction
          (UniversalVertex.CompositeDeckTransformation.baseSymmetry
            transformation)
          (Sum.inl point.vertex) =
        Sum.inl (level.automorphismAction.vertexAction
          (UniversalVertex.CompositeDeckTransformation.baseSymmetry
            transformation) point.vertex) := by
    rfl
  rw [compactVertexEquality] at equality
  rw [IncidenceNode.properIncidenceGraphHom_apply,
    IncidenceNode.properMap_vertex_original,
    IncidenceNode.properIncidenceGraphHom_apply,
    IncidenceNode.properMap_vertex_original] at equality
  change IncidenceNode.vertex (Sum.inl
      (level.projection.vertexMap
        (deckVertexMap diagram root level transformation point).vertex)) =
    IncidenceNode.vertex (Sum.inl
      (level.projection.vertexMap point.vertex)) at equality
  exact Sum.inl.inj (IncidenceNode.vertex.inj equality)

/-- Deck transformations preserve the projection of a lifted edge to the
source semigraph. -/
theorem deckEdgeMap_projection
    (transformation : DeckGroup diagram root level)
    (point : (Cover diagram root level).Edge) :
    level.projection.edgeMap
        (deckEdgeMap diagram root level transformation point).edge =
      level.projection.edgeMap point.edge := by
  have equality := baseIncidenceProjection_incidencePerm
    diagram root level
      (UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation)
      (IncidenceNode.edge point.edge)
  rw [IncidenceNode.incidencePerm_edge,
    IncidenceNode.properIncidenceGraphHom_apply,
    IncidenceNode.properIncidenceGraphHom_apply] at equality
  change IncidenceNode.edge
      (level.projection.edgeMap
        (deckEdgeMap diagram root level transformation point).edge) =
    IncidenceNode.edge (level.projection.edgeMap point.edge) at equality
  exact IncidenceNode.edge.inj equality

/-- Any two lifted vertices over the same source vertex differ by a complete
deck transformation. -/
theorem exists_deckVertexMap_eq
    (first second : (Cover diagram root level).Vertex)
    (sameProjection : level.projection.vertexMap first.vertex =
      level.projection.vertexMap second.vertex) :
    ∃ transformation : DeckGroup diagram root level,
      deckVertexMap diagram root level transformation first = second := by
  have sameFiber : compositeEndpoint diagram root level first.path =
      compositeEndpoint diagram root level second.path := by
    unfold compositeEndpoint
    rw [first.endpoint_eq, second.endpoint_eq,
      IncidenceNode.properIncidenceGraphHom_apply,
      IncidenceNode.properMap_vertex_original,
      IncidenceNode.properIncidenceGraphHom_apply,
      IncidenceNode.properMap_vertex_original]
    change IncidenceNode.vertex (Sum.inl
        (level.projection.vertexMap first.vertex)) =
      IncidenceNode.vertex (Sum.inl
        (level.projection.vertexMap second.vertex))
    rw [sameProjection]
  obtain ⟨transformation, pathEquality⟩ :=
    deckAction_transitive_compositeFiber diagram root level
      first.path second.path sameFiber
  refine ⟨transformation, ?_⟩
  apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
  exact pathEquality

/-- Any two lifted edges over the same source edge differ by a complete deck
transformation. -/
theorem exists_deckEdgeMap_eq
    (first second : (Cover diagram root level).Edge)
    (sameProjection : level.projection.edgeMap first.edge =
      level.projection.edgeMap second.edge) :
    ∃ transformation : DeckGroup diagram root level,
      deckEdgeMap diagram root level transformation first = second := by
  have sameFiber : compositeEndpoint diagram root level first.path =
      compositeEndpoint diagram root level second.path := by
    unfold compositeEndpoint
    rw [first.endpoint_eq, second.endpoint_eq,
      IncidenceNode.properIncidenceGraphHom_apply,
      IncidenceNode.properIncidenceGraphHom_apply]
    change IncidenceNode.edge (level.projection.edgeMap first.edge) =
      IncidenceNode.edge (level.projection.edgeMap second.edge)
    rw [sameProjection]
  obtain ⟨transformation, pathEquality⟩ :=
    deckAction_transitive_compositeFiber diagram root level
      first.path second.path sameFiber
  refine ⟨transformation, ?_⟩
  apply SourceSemiGraphUniversalCover.LiftedEdge.path_injective
  exact pathEquality

/-- The complete deck-group orbits of lifted vertices are exactly the fibers
over source vertices. -/
theorem deckVertex_orbitRel_iff_projection_eq
    (first second : (Cover diagram root level).Vertex) :
    letI := deckVertexMulAction diagram root level
    MulAction.orbitRel (DeckGroup diagram root level)
        (Cover diagram root level).Vertex first second ↔
      level.projection.vertexMap first.vertex =
        level.projection.vertexMap second.vertex := by
  letI := deckVertexMulAction diagram root level
  rw [MulAction.orbitRel_apply]
  constructor
  · intro sameOrbit
    obtain ⟨transformation, equality⟩ :=
      MulAction.mem_orbit_iff.mp sameOrbit
    rw [← equality]
    exact deckVertexMap_projection diagram root level transformation second
  · intro sameProjection
    obtain ⟨transformation, equality⟩ :=
      exists_deckVertexMap_eq diagram root level second first
        sameProjection.symm
    exact MulAction.mem_orbit_iff.mpr ⟨transformation, equality⟩

/-- The complete deck-group orbits of lifted edges are exactly the fibers
over source edges. -/
theorem deckEdge_orbitRel_iff_projection_eq
    (first second : (Cover diagram root level).Edge) :
    letI := deckEdgeMulAction diagram root level
    MulAction.orbitRel (DeckGroup diagram root level)
        (Cover diagram root level).Edge first second ↔
      level.projection.edgeMap first.edge =
        level.projection.edgeMap second.edge := by
  letI := deckEdgeMulAction diagram root level
  rw [MulAction.orbitRel_apply]
  constructor
  · intro sameOrbit
    obtain ⟨transformation, equality⟩ :=
      MulAction.mem_orbit_iff.mp sameOrbit
    rw [← equality]
    exact deckEdgeMap_projection diagram root level transformation second
  · intro sameProjection
    obtain ⟨transformation, equality⟩ :=
      exists_deckEdgeMap_eq diagram root level second first
        sameProjection.symm
    exact MulAction.mem_orbit_iff.mpr ⟨transformation, equality⟩

end

end Iut.SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover
