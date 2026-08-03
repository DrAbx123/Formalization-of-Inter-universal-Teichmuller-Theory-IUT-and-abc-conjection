/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedGaloisComponentMap
import Iut.Foundations.SourceFiniteSheetUniversalLift

/-!
# Coherent target points over a finite-level universal cover

The gluing isomorphisms of a geometric cover identify the underlying point
sets at adjacent vertices.  Connectedness of the base therefore lets us
trivialize every vertex and representative-edge carrier by the carrier over
one root vertex.  Conjugating the actual branch gluing by these arbitrary
trivializations produces branch permutations of one fixed sheet.

The universal semigraph lift then transports one chosen root target point to
compatible target points at every lifted vertex and edge.  This separates the
pure path-lifting argument from the later equivariant constituent maps.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceSemiGraphOfAnabelioids.CovObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})

/-- The underlying point-set equivalence supplied by target gluing across one
edge. -/
noncomputable def incidentVertexCarrierEquiv
    (target : diagram.CovObject) {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    (target.vertexObject first.vertex).obj.V.obj ≃
      (target.vertexObject second.vertex).obj.V.obj :=
  SourceFiniteLevelUniversalCover.actionCarrierEquiv
    (target.glue first second)

/-- Adjacent base vertices have equivalent target carriers. -/
theorem adjacentVertexCarrierEquiv_nonempty
    (target : diagram.CovObject) {first second : diagram.base.Vertex}
    (adjacent : diagram.base.Adjacent first second) :
    Nonempty ((target.vertexObject first).obj.V.obj ≃
      (target.vertexObject second).obj.V.obj) := by
  rcases adjacent with
    ⟨edge, firstBranch, secondBranch, _branchesDistinct,
      firstAbuts, secondAbuts⟩
  exact ⟨incidentVertexCarrierEquiv diagram target
    ⟨firstBranch, first, firstAbuts⟩
    ⟨secondBranch, second, secondAbuts⟩⟩

/-- A closed-edge path in the base identifies the target carriers at its
endpoints. -/
theorem pathVertexCarrierEquiv_nonempty
    (target : diagram.CovObject) {first second : diagram.base.Vertex}
    (path : Relation.ReflTransGen diagram.base.Adjacent first second) :
    Nonempty ((target.vertexObject first).obj.V.obj ≃
      (target.vertexObject second).obj.V.obj) := by
  induction path with
  | refl => exact ⟨Equiv.refl _⟩
  | @tail middle final path adjacent inductionHypothesis =>
      exact ⟨(Classical.choice inductionHypothesis).trans
        (Classical.choice
          (adjacentVertexCarrierEquiv_nonempty diagram target adjacent))⟩

/-- Connectedness supplies a carrier equivalence between any two vertex
constituents of a geometric cover. -/
theorem connectedVertexCarrierEquiv_nonempty
    (target : diagram.CovObject) (first second : diagram.base.Vertex) :
    Nonempty ((target.vertexObject first).obj.V.obj ≃
      (target.vertexObject second).obj.V.obj) := by
  rcases diagram.connected with connected | isolated
  · exact pathVertexCarrierEquiv_nonempty diagram target
      (connected.2.2 first second)
  · letI : IsEmpty diagram.base.Vertex := isolated.1
    exact isEmptyElim first

/-- A selected common-sheet trivialization of every target vertex carrier. -/
noncomputable def connectedVertexCarrierEquiv
    (target : diagram.CovObject) (first second : diagram.base.Vertex) :
    (target.vertexObject first).obj.V.obj ≃
      (target.vertexObject second).obj.V.obj :=
  Classical.choice
    (connectedVertexCarrierEquiv_nonempty diagram target first second)

namespace TargetSheetLift

variable (root : diagram.base.Vertex) (target : diagram.CovObject)

/-- The one fixed sheet used to trivialize the target point cover. -/
abbrev Sheet := (target.vertexObject root).obj.V.obj

/-- Trivialization at a base vertex. -/
noncomputable def vertexTrivialization (vertex : diagram.base.Vertex) :
    Sheet diagram root target ≃ (target.vertexObject vertex).obj.V.obj :=
  connectedVertexCarrierEquiv diagram target root vertex

/-- Trivialization of the representative target edge carrier. -/
noncomputable def edgeTrivialization (edge : diagram.base.Edge) :
    Sheet diagram root target ≃
      (coverEdgeObject diagram root target edge).obj.V.obj := by
  let reference := coverReferenceBranch diagram root edge
  exact vertexTrivialization diagram root target reference.vertex

/-- The actual target gluing, viewed as an equivalence from the representative
edge carrier to the carrier at an incident vertex. -/
noncomputable def branchCarrierEquiv
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    (coverEdgeObject diagram root target edge).obj.V.obj ≃
      (target.vertexObject branch.vertex).obj.V.obj := by
  let reference := coverReferenceBranch diagram root edge
  exact SourceFiniteLevelUniversalCover.actionCarrierEquiv
    (target.glue reference branch)

variable (object : diagram.GluedObject)

/-- The point obtained by carrying the canonical representative of a finite
edge orbit back through an incident finite branch comparison. -/
noncomputable def branchFiniteVertexPoint
    (edge : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Edge)
    (branch : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Branch edge)
    (vertex : diagram.base.Vertex)
    (abuts : diagram.base.coincidence edge.1 branch = some vertex) :
    ((diagram.vertexAnabelioid vertex).finiteAction
      (object.vertexObject vertex)).obj.V := by
  let incident : diagram.IncidentBranch edge.1 :=
    ⟨branch, vertex, abuts⟩
  let reference := coverReferenceBranch diagram root edge.1
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge.1).coverCategory
  exact (finiteBranchActionIso diagram root object incident).inv.hom.hom
    (finiteCanonicalEdgeComponentEquiv
      diagram root object edge.1 edge.2).out

/-- The branch-transported edge representative and the canonical
representative of its incident vertex orbit differ by a local group element.
This is the finite representative correction that must accompany target
gluing. -/
theorem branchRepresentativeCorrection_nonempty
    (edge : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Edge)
    (branch : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Branch edge)
    (vertex : diagram.base.Vertex)
    (abuts : diagram.base.coincidence edge.1 branch = some vertex) :
    Nonempty { element : (diagram.vertexAnabelioid vertex).group //
      element •
          (finiteVertexComponentEquiv diagram root object vertex
            (SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
              diagram root object
              ⟨branch, vertex, abuts⟩ edge.2)).out =
        branchFiniteVertexPoint
          diagram root object edge branch vertex abuts } := by
  let incident : diagram.IncidentBranch edge.1 :=
    ⟨branch, vertex, abuts⟩
  let reference := coverReferenceBranch diagram root edge.1
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge.1).coverCategory
  let edgeComponent := finiteCanonicalEdgeComponentEquiv
    diagram root object edge.1 edge.2
  let restrictedComponent :=
    (sourceFiniteActionComponentEquiv
      (finiteBranchActionIso diagram root object incident)).symm edgeComponent
  have restrictedComponent_eq : restrictedComponent =
      Quotient.mk'' (branchFiniteVertexPoint
        diagram root object edge branch vertex abuts) := by
    change (sourceFiniteActionComponentEquiv
        (finiteBranchActionIso diagram root object incident)).symm
          edgeComponent = Quotient.mk'' _
    rw [← Quotient.out_eq' edgeComponent]
    rfl
  have compatibility := finiteBranchComponentCompatibility
    diagram root object incident edge.2
  have compatibility' :
      sourceFiniteRestrictionComponentMap
          (diagram.branchMorphism branch abuts).fundamentalGroupHom
          ((diagram.vertexAnabelioid vertex).finiteAction
            (object.vertexObject vertex)) restrictedComponent =
        finiteVertexComponentEquiv diagram root object vertex
          (SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
            diagram root object incident edge.2) := by
    simpa only [incident, restrictedComponent] using compatibility
  rw [restrictedComponent_eq] at compatibility'
  change Quotient.mk'' (branchFiniteVertexPoint
      diagram root object edge branch vertex abuts) =
    finiteVertexComponentEquiv diagram root object vertex
      (SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
        diagram root object incident edge.2) at compatibility'
  let vertexComponent := finiteVertexComponentEquiv diagram root object vertex
    (SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
      diagram root object incident edge.2)
  have quotientEquality :
      Quotient.mk'' vertexComponent.out =
        Quotient.mk'' (branchFiniteVertexPoint
          diagram root object edge branch vertex abuts) :=
    (Quotient.out_eq' vertexComponent).trans compatibility'.symm
  have relation := Quotient.exact quotientEquality.symm
  change branchFiniteVertexPoint
      diagram root object edge branch vertex abuts ∈
        MulAction.orbit (diagram.vertexAnabelioid vertex).group
          vertexComponent.out at relation
  rcases relation with ⟨element, equality⟩
  exact ⟨⟨element, equality⟩⟩

/-- A chosen local group element correcting the finite representative change
across an incident branch. -/
noncomputable def branchRepresentativeCorrection
    (edge : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Edge)
    (branch : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Branch edge)
    (vertex : diagram.base.Vertex)
    (abuts : diagram.base.coincidence edge.1 branch = some vertex) :
    (diagram.vertexAnabelioid vertex).group :=
  Classical.choice
    (branchRepresentativeCorrection_nonempty
      diagram root object edge branch vertex abuts) |>.1

/-- The selected correction carries the canonical vertex-orbit
representative to the branch-transported canonical edge representative. -/
theorem branchRepresentativeCorrection_spec
    (edge : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Edge)
    (branch : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Branch edge)
    (vertex : diagram.base.Vertex)
    (abuts : diagram.base.coincidence edge.1 branch = some vertex) :
    branchRepresentativeCorrection
        diagram root object edge branch vertex abuts •
      (finiteVertexComponentEquiv diagram root object vertex
        (SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
          diagram root object
          ⟨branch, vertex, abuts⟩ edge.2)).out =
      branchFiniteVertexPoint
        diagram root object edge branch vertex abuts :=
  (Classical.choice
    (branchRepresentativeCorrection_nonempty
      diagram root object edge branch vertex abuts)).2

/-- Conjugate target gluing by the selected carrier trivializations and
correct the change between the chosen finite edge and vertex orbit
representatives.  An open branch has no incidence constraint, so its unused
permutation is the identity.
-/
noncomputable def transport
    (edge : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Edge)
    (branch : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Branch edge) :
    Equiv.Perm (Sheet diagram root target) := by
  match abuts : diagram.base.coincidence edge.1 branch with
  | none => exact Equiv.refl _
  | some vertex =>
      let incident : diagram.IncidentBranch edge.1 :=
        ⟨branch, vertex, abuts⟩
      exact (edgeTrivialization diagram root target edge.1).trans
        ((branchCarrierEquiv diagram root target incident).trans
          ((MulAction.toPermHom
              (diagram.vertexAnabelioid vertex).group
              (target.vertexObject vertex).obj.V.obj
              ((branchRepresentativeCorrection
                diagram root object edge branch vertex abuts)⁻¹)).trans
            (vertexTrivialization diagram root target vertex).symm))

/-- Evaluation of the conjugated branch transport at a verticial branch. -/
theorem transport_apply_of_some
    (edge : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Edge)
    (branch : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Branch edge)
    (vertex : diagram.base.Vertex)
    (abuts : diagram.base.coincidence edge.1 branch = some vertex)
    (sheet : Sheet diagram root target) :
    transport diagram root target object edge branch sheet =
      (vertexTrivialization diagram root target vertex).symm
        ((branchRepresentativeCorrection
            diagram root object edge branch vertex abuts)⁻¹ •
          branchCarrierEquiv diagram root target
            ⟨branch, vertex, abuts⟩
            (edgeTrivialization diagram root target edge.1 sheet)) := by
  unfold transport
  split
  next noVertex =>
    rw [abuts] at noVertex
    contradiction
  next actualVertex actualAbuts =>
    have equality : actualVertex = vertex :=
      Option.some.inj (actualAbuts.symm.trans abuts)
    subst actualVertex
    rfl

variable (levelRoot : (SourceFiniteLevelUniversalCover.LevelSemiGraph
  diagram root object).Vertex)
    (initial : Sheet diagram root target)

/-- The common sheet transported to a lifted universal vertex. -/
noncomputable def vertexSheet
    (vertex : SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedVertex
      (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
      levelRoot) : Sheet diagram root target :=
  (SourceFiniteSheetSemiGraphCover.UniversalLift.vertexMap
    (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
    (Sheet diagram root target) (transport diagram root target object)
    levelRoot initial vertex).2

/-- The common sheet transported to a lifted universal edge. -/
noncomputable def edgeSheet
    (edge : SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
      (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
      levelRoot) : Sheet diagram root target :=
  (SourceFiniteSheetSemiGraphCover.UniversalLift.edgeMap
    (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
    (Sheet diagram root target) (transport diagram root target object)
    levelRoot initial edge).2

/-- The target point selected at a lifted universal vertex. -/
noncomputable def vertexPoint
    (vertex : SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedVertex
      (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
      levelRoot) :
    (target.vertexObject vertex.vertex.1).obj.V.obj :=
  vertexTrivialization diagram root target vertex.vertex.1
    (vertexSheet diagram root target object levelRoot initial vertex)

/-- The target point selected at a lifted universal edge. -/
noncomputable def edgePoint
    (edge : SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
      (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
      levelRoot) :
    (coverEdgeObject diagram root target edge.edge.1).obj.V.obj :=
  edgeTrivialization diagram root target edge.edge.1
    (edgeSheet diagram root target object levelRoot initial edge)

/-- After correcting the canonical finite-orbit representative, the selected
vertex and edge points satisfy the actual target gluing at every lifted
incidence. -/
theorem branchCarrierEquiv_edgePoint
    (edge : SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
      (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
      levelRoot)
    (branch : (SourceFiniteLevelUniversalCover.LevelSemiGraph
      diagram root object).Branch edge.edge)
    (vertex : SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedVertex
      (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
      levelRoot)
    (coincidence :
      (SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.semiGraphCover
        (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
        levelRoot).coincidence edge branch = some vertex) :
    let abuts : diagram.base.coincidence edge.edge.1 branch =
        some vertex.vertex.1 :=
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverProjection
        diagram root object).map_coincidence edge.edge branch vertex.vertex
        ((SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.projection
          (SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object)
          levelRoot).map_coincidence edge branch vertex coincidence)
    branchRepresentativeCorrection diagram root object edge.edge branch
        vertex.vertex.1 abuts •
      vertexPoint diagram root target object levelRoot initial vertex =
        branchCarrierEquiv diagram root target
          ⟨branch, vertex.vertex.1, abuts⟩
          (edgePoint diagram root target object levelRoot initial edge) := by
  let base := SourceFiniteLevelUniversalCover.LevelSemiGraph
    diagram root object
  let universalProjection :=
    SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.projection
      base levelRoot
  let levelProjection :=
    SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverProjection
      diagram root object
  let levelCoincidence : base.coincidence edge.edge branch =
      some vertex.vertex :=
    universalProjection.map_coincidence edge branch vertex coincidence
  let abuts : diagram.base.coincidence edge.edge.1 branch =
      some vertex.vertex.1 :=
    levelProjection.map_coincidence edge.edge branch vertex.vertex
      levelCoincidence
  dsimp only
  have sheetEquality :=
    SourceFiniteSheetSemiGraphCover.UniversalLift.vertexSheet_eq_transport_of_coincidence
      base (Sheet diagram root target) (transport diagram root target object)
      levelRoot initial edge branch vertex coincidence
  change vertexSheet diagram root target object levelRoot initial vertex =
      transport diagram root target object edge.edge branch
        (edgeSheet diagram root target object levelRoot initial edge)
      at sheetEquality
  change branchRepresentativeCorrection diagram root object edge.edge branch
        vertex.vertex.1 abuts •
      vertexTrivialization diagram root target vertex.vertex.1
        (vertexSheet diagram root target object levelRoot initial vertex) =
    branchCarrierEquiv diagram root target
      ⟨branch, vertex.vertex.1, abuts⟩
      (edgeTrivialization diagram root target edge.edge.1
        (edgeSheet diagram root target object levelRoot initial edge))
  rw [sheetEquality]
  rw [transport_apply_of_some diagram root target object edge.edge branch
    vertex.vertex.1 abuts]
  rw [Equiv.apply_symm_apply]
  simp

end TargetSheetLift

end SourceSemiGraphOfAnabelioids.CovObject

end Iut
