/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedTargetSheetLift

/-!
# Geometric domination by a finite-level universal cover

A connected pointed Galois level that splits a geometric tempered cover gives
equivariant maps from every repeated finite orbit of its universal cover to
the corresponding target constituent.  The corrected target-sheet lift makes
these local maps commute with the literal branch gluing, so they assemble into
a morphism in `B^cov(G)`.
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

namespace SourceSemiGraphOfAnabelioids.CovObject

/-- Two equivariant maps out of a repeated family of finite orbit components
are equal when they agree on the canonical representative of every copied
component. -/
theorem sourceTemperoidComponentFamilyHom_ext
    (G : ProfiniteGrp.{u}) (source : ContAction FintypeCat.{u} G)
    (target : SourceTemperoidAction G)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent G source)
    (first second :
      sourceTemperoidComponentFamilyAction
        G source Index component ⟶ target)
    (base : ∀ index,
      first.hom.hom
          ⟨index, ⟨(component index).out,
            Quotient.out_eq' (component index)⟩⟩ =
        second.hom.hom
          ⟨index, ⟨(component index).out,
            Quotient.out_eq' (component index)⟩⟩) :
    first = second := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  let canonical : SourceActionComponentFiber G source
      (component point.1) :=
    ⟨(component point.1).out, Quotient.out_eq' (component point.1)⟩
  obtain ⟨element, equality⟩ :=
    (sourceActionComponentAction_pretransitive
      G source (component point.1)).exists_smul_eq canonical point.2
  let canonicalFamilyPoint :
      SourceTemperoidComponentFamilyCarrier G source Index component :=
    ⟨point.1, canonical⟩
  have familyEquality : element • canonicalFamilyPoint = point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq equality
  have firstEquivariance := ConcreteCategory.congr_hom
    (first.hom.comm element) canonicalFamilyPoint
  have secondEquivariance := ConcreteCategory.congr_hom
    (second.hom.comm element) canonicalFamilyPoint
  rw [← familyEquality]
  exact firstEquivariance.trans <|
    (congrArg (element • ·) (base point.1)).trans secondEquivariance.symm

namespace GeometricDomination

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target)
    (initial : (target.vertexObject root).obj.V.obj)

/-- The edge stabilizer criterion in the canonical finite edge-action model,
rather than the restriction-of-the-reference-vertex model used by
`coverEdgeObject`. -/
theorem canonicalEdgeStabilizerFixesTarget
    (split : IsSplitBy diagram root level.object target)
    (edge : diagram.base.Edge)
    (sourcePoint : ((diagram.edgeAnabelioid edge).finiteAction
      (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
        diagram root level.object edge)).obj.V.obj)
    (element : (diagram.edgeAnabelioid edge).group)
    (fixes : element • sourcePoint = sourcePoint) :
    ∀ targetPoint : (coverEdgeObject diagram root target edge).obj.V.obj,
      element • targetPoint = targetPoint := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  let comparison := finiteBranchActionIso diagram root level.object reference
  let restrictedPoint := comparison.inv.hom.hom sourcePoint
  have restrictedFixes : element • restrictedPoint = restrictedPoint := by
    change element • comparison.inv.hom.hom sourcePoint =
      comparison.inv.hom.hom sourcePoint
    exact (ConcreteCategory.congr_hom
      (comparison.inv.hom.comm element) sourcePoint).symm.trans
        (congrArg comparison.inv.hom.hom fixes)
  exact galoisEdgeStabilizerFixesTarget level target split edge
    restrictedPoint element restrictedFixes

/-- The constituent map at a base vertex, obtained by mapping each selected
finite orbit to its coherently lifted target point. -/
noncomputable def vertexHom
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (vertex : diagram.base.Vertex) :
    SourceFiniteLevelUniversalCover.vertexAction
        diagram root level.object level.rootVertex vertex ⟶
      target.vertexObject vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact sourceTemperoidComponentFamilyHomOfStabilizerFixes
    (diagram.vertexAnabelioid vertex).group
    ((diagram.vertexAnabelioid vertex).finiteAction
      (level.object.vertexObject vertex))
    (target.vertexObject vertex)
    (SourceFiniteLevelUniversalCover.VertexIndex
      diagram root level.object level.rootVertex vertex)
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root level.object level.rootVertex vertex)
    (fun index ↦ index.2 ▸
      TargetSheetLift.vertexPoint diagram root target level.object
        level.rootVertex initial index.1)
    (fun index element fixes ↦
      galoisVertexStabilizerFixesTarget level target split vertex
        (SourceFiniteLevelUniversalCover.selectedVertexComponent
          diagram root level.object level.rootVertex vertex index).out
        element fixes
        (index.2 ▸ TargetSheetLift.vertexPoint diagram root target level.object
          level.rootVertex initial index.1))

/-- The analogous map on the common representative edge constituent. -/
noncomputable def edgeHom
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (edge : diagram.base.Edge) :
    SourceFiniteLevelUniversalCover.edgeAction
        diagram root level.object level.rootVertex edge ⟶
      coverEdgeObject diagram root target edge := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact sourceTemperoidComponentFamilyHomOfStabilizerFixes
    (diagram.edgeAnabelioid edge).group
    ((diagram.edgeAnabelioid edge).finiteAction
      (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
        diagram root level.object edge))
    (coverEdgeObject diagram root target edge)
    (SourceFiniteLevelUniversalCover.EdgeIndex
      diagram root level.object level.rootVertex edge)
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root level.object level.rootVertex edge)
    (fun index ↦ index.2 ▸
      TargetSheetLift.edgePoint diagram root target level.object
        level.rootVertex initial index.1)
    (fun index element fixes ↦
      canonicalEdgeStabilizerFixesTarget
        diagram root level target split edge
        (SourceFiniteLevelUniversalCover.selectedEdgeComponent
          diagram root level.object level.rootVertex edge index).out
        element fixes
        (index.2 ▸ TargetSheetLift.edgePoint diagram root target level.object
          level.rootVertex initial index.1))

/-- Evaluation of the vertex constituent map at the canonical representative
of a copied finite orbit. -/
theorem vertexHom_base
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (vertex : diagram.base.Vertex)
    (index : SourceFiniteLevelUniversalCover.VertexIndex
      diagram root level.object level.rootVertex vertex) :
    (vertexHom diagram root level target split initial vertex).hom.hom
        ⟨index,
          ⟨(SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root level.object level.rootVertex vertex index).out,
            Quotient.out_eq'
              (SourceFiniteLevelUniversalCover.selectedVertexComponent
                diagram root level.object level.rootVertex vertex index)⟩⟩ =
      index.2 ▸ TargetSheetLift.vertexPoint diagram root target level.object
        level.rootVertex initial index.1 := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  unfold vertexHom
  exact sourceTemperoidComponentFamilyHomOfStabilizerFixes_base
    (diagram.vertexAnabelioid vertex).group
    ((diagram.vertexAnabelioid vertex).finiteAction
      (level.object.vertexObject vertex))
    (target.vertexObject vertex)
    (SourceFiniteLevelUniversalCover.VertexIndex
      diagram root level.object level.rootVertex vertex)
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root level.object level.rootVertex vertex)
    (fun targetIndex ↦ targetIndex.2 ▸
      TargetSheetLift.vertexPoint diagram root target level.object
        level.rootVertex initial targetIndex.1)
    _ index

/-- Evaluation of the edge constituent map at the canonical representative
of a copied finite edge orbit. -/
theorem edgeHom_base
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (edge : diagram.base.Edge)
    (index : SourceFiniteLevelUniversalCover.EdgeIndex
      diagram root level.object level.rootVertex edge) :
    (edgeHom diagram root level target split initial edge).hom.hom
        ⟨index,
          ⟨(SourceFiniteLevelUniversalCover.selectedEdgeComponent
            diagram root level.object level.rootVertex edge index).out,
            Quotient.out_eq'
              (SourceFiniteLevelUniversalCover.selectedEdgeComponent
                diagram root level.object level.rootVertex edge index)⟩⟩ =
      index.2 ▸ TargetSheetLift.edgePoint diagram root target level.object
        level.rootVertex initial index.1 := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  unfold edgeHom
  exact sourceTemperoidComponentFamilyHomOfStabilizerFixes_base
    (diagram.edgeAnabelioid edge).group
    ((diagram.edgeAnabelioid edge).finiteAction
      (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
        diagram root level.object edge))
    (coverEdgeObject diagram root target edge)
    (SourceFiniteLevelUniversalCover.EdgeIndex
      diagram root level.object level.rootVertex edge)
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root level.object level.rootVertex edge)
    (fun targetIndex ↦ targetIndex.2 ▸
      TargetSheetLift.edgePoint diagram root target level.object
        level.rootVertex initial targetIndex.1)
    _ index

/-- The canonical point in the copied finite edge orbit indexed by a lifted
universal edge. -/
noncomputable def edgeBasePoint
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (edge : diagram.base.Edge)
    (index : SourceFiniteLevelUniversalCover.EdgeIndex
      diagram root level.object level.rootVertex edge) :
    (SourceFiniteLevelUniversalCover.edgeAction
      diagram root level.object level.rootVertex edge).obj.V.obj :=
  ⟨index,
    ⟨(SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root level.object level.rootVertex edge index).out,
      Quotient.out_eq'
        (SourceFiniteLevelUniversalCover.selectedEdgeComponent
          diagram root level.object level.rootVertex edge index)⟩⟩

/-- Pulling a canonical copied edge representative back through the branch
comparison recovers the incident lifted-vertex index. -/
theorem branchEdgeFamilyIso_inv_edgeBasePoint_fst
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (liftedEdge :
      SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
        (SourceFiniteLevelUniversalCover.LevelSemiGraph
          diagram root level.object) level.rootVertex)
    (branch : diagram.IncidentBranch liftedEdge.edge.1) :
    ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root level.object level.rootVertex branch).inv.hom.hom
      (edgeBasePoint diagram root level
        liftedEdge.edge.1 ⟨liftedEdge, rfl⟩)).1 =
      (SourceFiniteLevelUniversalCover.edgeIndexToRestrictedBranchIndex
        diagram root level.object level.rootVertex branch
          ⟨liftedEdge, rfl⟩).1 := by
  rfl

/-- The point coordinate of that pullback is precisely the canonical edge
representative transported back through the finite branch comparison. -/
theorem branchEdgeFamilyIso_inv_edgeBasePoint_val
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (liftedEdge :
      SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
        (SourceFiniteLevelUniversalCover.LevelSemiGraph
          diagram root level.object) level.rootVertex)
    (branch : diagram.IncidentBranch liftedEdge.edge.1) :
    ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root level.object level.rootVertex branch).inv.hom.hom
      (edgeBasePoint diagram root level
        liftedEdge.edge.1 ⟨liftedEdge, rfl⟩)).2.1 =
      TargetSheetLift.branchFiniteVertexPoint diagram root level.object
        liftedEdge.edge branch.branch branch.vertex branch.abuts := by
  let reference := coverReferenceBranch diagram root liftedEdge.edge.1
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid liftedEdge.edge.1).coverCategory
  let restrictedIso := sourceRestrictedComponentFamilyActionIso
    (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
    ((diagram.vertexAnabelioid branch.vertex).finiteAction
      (level.object.vertexObject branch.vertex))
    (SourceFiniteLevelUniversalCover.VertexIndex
      diagram root level.object level.rootVertex branch.vertex)
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root level.object level.rootVertex branch.vertex)
  let familyIso := sourceTemperoidComponentFamilyActionIso
    (finiteBranchActionIso diagram root level.object branch)
    (fun index : SourceFiniteLevelUniversalCover.RestrictedBranchIndex
      diagram root level.object level.rootVertex branch ↦ index.2.1)
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root level.object level.rootVertex liftedEdge.edge.1)
    (SourceFiniteLevelUniversalCover.restrictedBranchIndexEquivEdgeIndex
      diagram root level.object level.rootVertex branch)
    (SourceFiniteLevelUniversalCover.branchComponentCompatibility
      diagram root level.object level.rootVertex branch)
  let point := edgeBasePoint diagram root level
    liftedEdge.edge.1 ⟨liftedEdge, rfl⟩
  have restrictedValue := sourceRestrictedComponentFamilyActionIso_inv_apply_val
    (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
    ((diagram.vertexAnabelioid branch.vertex).finiteAction
      (level.object.vertexObject branch.vertex))
    (SourceFiniteLevelUniversalCover.VertexIndex
      diagram root level.object level.rootVertex branch.vertex)
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root level.object level.rootVertex branch.vertex)
    (familyIso.inv.hom.hom point)
  have familyValue := sourceTemperoidComponentFamilyActionIso_inv_apply_val
    (finiteBranchActionIso diagram root level.object branch)
    (fun index : SourceFiniteLevelUniversalCover.RestrictedBranchIndex
      diagram root level.object level.rootVertex branch ↦ index.2.1)
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root level.object level.rootVertex liftedEdge.edge.1)
    (SourceFiniteLevelUniversalCover.restrictedBranchIndexEquivEdgeIndex
      diagram root level.object level.rootVertex branch)
    (SourceFiniteLevelUniversalCover.branchComponentCompatibility
      diagram root level.object level.rootVertex branch)
    point
  have restrictedValue' :
      ((SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex branch).inv.hom.hom
        point).2.1 = (familyIso.inv.hom.hom point).2.1 := by
    change (restrictedIso.inv.hom.hom
      (familyIso.inv.hom.hom point)).2.1 =
        (familyIso.inv.hom.hom point).2.1
    exact restrictedValue
  rw [restrictedValue', familyValue]
  rfl

/-- The finite representative correction carries the canonical vertex
representative selected by the decoded incidence to the point obtained by
pulling back the canonical edge representative. -/
theorem branchRepresentativeCorrection_smul_branchPreimageBase
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (liftedEdge :
      SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
        (SourceFiniteLevelUniversalCover.LevelSemiGraph
          diagram root level.object) level.rootVertex)
    (branch : diagram.IncidentBranch liftedEdge.edge.1) :
    let pulled :=
      (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root level.object level.rootVertex branch).inv.hom.hom
          (edgeBasePoint diagram root level
            liftedEdge.edge.1 ⟨liftedEdge, rfl⟩)
    TargetSheetLift.branchRepresentativeCorrection diagram root level.object
        liftedEdge.edge branch.branch branch.vertex branch.abuts •
      (SourceFiniteLevelUniversalCover.selectedVertexComponent
        diagram root level.object level.rootVertex branch.vertex pulled.1).out =
      pulled.2.1 := by
  rcases branch with ⟨branchValue, vertex, abuts⟩
  dsimp only
  let incident : diagram.IncidentBranch liftedEdge.edge.1 :=
    ⟨branchValue, vertex, abuts⟩
  let pulled :=
    (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root level.object level.rootVertex incident).inv.hom.hom
        (edgeBasePoint diagram root level
          liftedEdge.edge.1 ⟨liftedEdge, rfl⟩)
  let decoded :=
    SourceFiniteLevelUniversalCover.edgeIndexToRestrictedBranchIndex
      diagram root level.object level.rootVertex incident ⟨liftedEdge, rfl⟩
  have indexEquality : pulled.1 = decoded.1 :=
    branchEdgeFamilyIso_inv_edgeBasePoint_fst
      diagram root level liftedEdge incident
  have valueEquality : pulled.2.1 =
      TargetSheetLift.branchFiniteVertexPoint diagram root level.object
        liftedEdge.edge branchValue vertex abuts :=
    branchEdgeFamilyIso_inv_edgeBasePoint_val
      diagram root level liftedEdge incident
  have representativeEquality := congrArg
    (fun index ↦
      (SourceFiniteLevelUniversalCover.selectedVertexComponent
        diagram root level.object level.rootVertex vertex index).out)
    indexEquality
  change (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root level.object level.rootVertex vertex pulled.1).out =
    (SourceFiniteLevelUniversalCover.selectedVertexComponent
      diagram root level.object level.rootVertex vertex decoded.1).out
    at representativeEquality
  change TargetSheetLift.branchRepresentativeCorrection
        diagram root level.object liftedEdge.edge branchValue vertex abuts •
      (SourceFiniteLevelUniversalCover.selectedVertexComponent
        diagram root level.object level.rootVertex vertex pulled.1).out =
    pulled.2.1
  rw [representativeEquality, valueEquality]
  unfold decoded
  unfold SourceFiniteLevelUniversalCover.edgeIndexToRestrictedBranchIndex
  unfold SourceFiniteLevelUniversalCover.liftedEdgeToRestrictedBranchIndex
  unfold SourceFiniteLevelUniversalCover.selectedVertexComponent
  exact TargetSheetLift.branchRepresentativeCorrection_spec
    diagram root level.object liftedEdge.edge branchValue vertex abuts

/-- The vertex constituent map sends the branch-preimage of the canonical
edge representative to the corrected selected target vertex point. -/
theorem vertexHom_branchPreimageBase
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (liftedEdge :
      SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
        (SourceFiniteLevelUniversalCover.LevelSemiGraph
          diagram root level.object) level.rootVertex)
    (branch : diagram.IncidentBranch liftedEdge.edge.1) :
    let pulled :=
      (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
        diagram root level.object level.rootVertex branch).inv.hom.hom
          (edgeBasePoint diagram root level
            liftedEdge.edge.1 ⟨liftedEdge, rfl⟩)
    (vertexHom diagram root level target split initial branch.vertex).hom.hom
        pulled =
      TargetSheetLift.branchRepresentativeCorrection
          diagram root level.object liftedEdge.edge branch.branch
            branch.vertex branch.abuts •
        (pulled.1.2 ▸ TargetSheetLift.vertexPoint
          diagram root target level.object level.rootVertex initial
            pulled.1.1) := by
  dsimp only
  let pulled :=
    (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root level.object level.rootVertex branch).inv.hom.hom
        (edgeBasePoint diagram root level
          liftedEdge.edge.1 ⟨liftedEdge, rfl⟩)
  let correction := TargetSheetLift.branchRepresentativeCorrection
    diagram root level.object liftedEdge.edge branch.branch
      branch.vertex branch.abuts
  let canonical :
      (SourceFiniteLevelUniversalCover.vertexAction
        diagram root level.object level.rootVertex branch.vertex).obj.V.obj :=
    ⟨pulled.1,
      ⟨(SourceFiniteLevelUniversalCover.selectedVertexComponent
        diagram root level.object level.rootVertex branch.vertex pulled.1).out,
        Quotient.out_eq'
          (SourceFiniteLevelUniversalCover.selectedVertexComponent
            diagram root level.object level.rootVertex
              branch.vertex pulled.1)⟩⟩
  have sourceEquality : correction • canonical = pulled := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact branchRepresentativeCorrection_smul_branchPreimageBase
        diagram root level liftedEdge branch
  have equivariance := ConcreteCategory.congr_hom
    ((vertexHom diagram root level target split initial
      branch.vertex).hom.comm correction) canonical
  calc
    (vertexHom diagram root level target split initial branch.vertex).hom.hom
        pulled =
      (vertexHom diagram root level target split initial branch.vertex).hom.hom
        (correction • canonical) := congrArg _ sourceEquality.symm
    _ = correction •
        (vertexHom diagram root level target split initial
          branch.vertex).hom.hom canonical := equivariance
    _ = correction •
        (pulled.1.2 ▸ TargetSheetLift.vertexPoint
          diagram root target level.object level.rootVertex initial
            pulled.1.1) := congrArg (correction • ·)
      (vertexHom_base diagram root level target split initial
        branch.vertex pulled.1)

/-- The decoded vertex of a canonical edge copy is the actual incident
universal-cover vertex at the selected branch. -/
theorem liftedEdge_coincidence_at_branch
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (liftedEdge :
      SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
        (SourceFiniteLevelUniversalCover.LevelSemiGraph
          diagram root level.object) level.rootVertex)
    (branch : diagram.IncidentBranch liftedEdge.edge.1) :
    let decoded :=
      SourceFiniteLevelUniversalCover.edgeIndexToRestrictedBranchIndex
        diagram root level.object level.rootVertex branch ⟨liftedEdge, rfl⟩
    (SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.semiGraphCover
      (SourceFiniteLevelUniversalCover.LevelSemiGraph
        diagram root level.object) level.rootVertex).coincidence
        liftedEdge branch.branch = some decoded.1.1 := by
  rcases branch with ⟨branchValue, vertex, abuts⟩
  dsimp only
  rw [SourceFiniteLevelUniversalCover.edgeIndexToRestrictedBranchIndex_refl]
  unfold SourceFiniteLevelUniversalCover.liftedEdgeToRestrictedBranchIndex
  exact SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.coincidence_eq_some_of_eq_some
      (SourceFiniteLevelUniversalCover.LevelSemiGraph
        diagram root level.object) level.rootVertex liftedEdge branchValue
      ⟨vertex, SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
        diagram root level.object ⟨branchValue, vertex, abuts⟩
          liftedEdge.edge.2⟩
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph_coincidence_of_some
          diagram root level.object abuts)

/-- The corrected target point at the decoded incident vertex is carried by
the literal target gluing to the selected target edge point. -/
theorem correctedTargetPoints_at_branch
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (liftedEdge :
      SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
        (SourceFiniteLevelUniversalCover.LevelSemiGraph
          diagram root level.object) level.rootVertex)
    (branch : diagram.IncidentBranch liftedEdge.edge.1) :
    let decoded :=
      SourceFiniteLevelUniversalCover.edgeIndexToRestrictedBranchIndex
        diagram root level.object level.rootVertex branch ⟨liftedEdge, rfl⟩
    TargetSheetLift.branchRepresentativeCorrection diagram root level.object
        liftedEdge.edge branch.branch branch.vertex branch.abuts •
      (decoded.1.2 ▸ TargetSheetLift.vertexPoint
        diagram root target level.object level.rootVertex initial
          decoded.1.1) =
      TargetSheetLift.branchCarrierEquiv diagram root target branch
        (TargetSheetLift.edgePoint diagram root target level.object
          level.rootVertex initial liftedEdge) := by
  rcases branch with ⟨branchValue, vertex, abuts⟩
  dsimp only
  let incident : diagram.IncidentBranch liftedEdge.edge.1 :=
    ⟨branchValue, vertex, abuts⟩
  let decoded :=
    SourceFiniteLevelUniversalCover.edgeIndexToRestrictedBranchIndex
      diagram root level.object level.rootVertex incident ⟨liftedEdge, rfl⟩
  change TargetSheetLift.branchRepresentativeCorrection
        diagram root level.object liftedEdge.edge branchValue vertex abuts •
      (decoded.1.2 ▸ TargetSheetLift.vertexPoint
        diagram root target level.object level.rootVertex initial
          decoded.1.1) =
    TargetSheetLift.branchCarrierEquiv diagram root target incident
      (TargetSheetLift.edgePoint diagram root target level.object
        level.rootVertex initial liftedEdge)
  have coincidence := liftedEdge_coincidence_at_branch
    diagram root level liftedEdge incident
  change (SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.semiGraphCover
      (SourceFiniteLevelUniversalCover.LevelSemiGraph
        diagram root level.object) level.rootVertex).coincidence
      liftedEdge branchValue = some decoded.1.1 at coincidence
  rcases decoded with
    ⟨⟨decodedVertex, vertexEquality⟩, restrictedComponent⟩
  cases vertexEquality
  have compatibility := TargetSheetLift.branchCarrierEquiv_edgePoint
    diagram root target level.object level.rootVertex initial
      liftedEdge branchValue decodedVertex coincidence
  simpa only [incident] using compatibility

/-- At one incident branch, the edge constituent map is the vertex
constituent map transported through the source and target branch
comparisons. -/
theorem branchHalfNaturality
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    edgeHom diagram root level target split initial edge =
      (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
          diagram root level.object level.rootVertex branch).inv ≫
        branch.temperoidPullback.map
          (vertexHom diagram root level target split initial branch.vertex) ≫
        (target.glue branch (coverReferenceBranch diagram root edge)).hom := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  apply sourceTemperoidComponentFamilyHom_ext
    (diagram.edgeAnabelioid edge).group
    ((diagram.edgeAnabelioid edge).finiteAction
      (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
        diagram root level.object edge))
    (coverEdgeObject diagram root target edge)
    (SourceFiniteLevelUniversalCover.EdgeIndex
      diagram root level.object level.rootVertex edge)
    (SourceFiniteLevelUniversalCover.selectedEdgeComponent
      diagram root level.object level.rootVertex edge)
  intro index
  rcases index with ⟨liftedEdge, edgeEquality⟩
  change liftedEdge.edge.1 = edge at edgeEquality
  cases edgeEquality
  let basePoint := edgeBasePoint diagram root level
    liftedEdge.edge.1 ⟨liftedEdge, rfl⟩
  let pulled :=
    (SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
      diagram root level.object level.rootVertex branch).inv.hom.hom basePoint
  let decoded :=
    SourceFiniteLevelUniversalCover.edgeIndexToRestrictedBranchIndex
      diagram root level.object level.rootVertex branch ⟨liftedEdge, rfl⟩
  have indexEquality : pulled.1 = decoded.1 :=
    branchEdgeFamilyIso_inv_edgeBasePoint_fst
      diagram root level liftedEdge branch
  have targetPointEquality :
      pulled.1.2 ▸ TargetSheetLift.vertexPoint
          diagram root target level.object level.rootVertex initial
            pulled.1.1 =
        decoded.1.2 ▸ TargetSheetLift.vertexPoint
          diagram root target level.object level.rootVertex initial
            decoded.1.1 :=
    congrArg
      (fun targetIndex : SourceFiniteLevelUniversalCover.VertexIndex
          diagram root level.object level.rootVertex branch.vertex ↦
        targetIndex.2 ▸ TargetSheetLift.vertexPoint
          diagram root target level.object level.rootVertex initial
            targetIndex.1)
      indexEquality
  have vertexEvaluation := vertexHom_branchPreimageBase
    diagram root level target split initial liftedEdge branch
  change (vertexHom diagram root level target split initial
      branch.vertex).hom.hom pulled =
    TargetSheetLift.branchRepresentativeCorrection
        diagram root level.object liftedEdge.edge branch.branch
          branch.vertex branch.abuts •
      (pulled.1.2 ▸ TargetSheetLift.vertexPoint
        diagram root target level.object level.rootVertex initial
          pulled.1.1) at vertexEvaluation
  rw [targetPointEquality] at vertexEvaluation
  have targetCompatibility := correctedTargetPoints_at_branch
    diagram root level target initial liftedEdge branch
  change TargetSheetLift.branchRepresentativeCorrection
      diagram root level.object liftedEdge.edge branch.branch
        branch.vertex branch.abuts •
      (decoded.1.2 ▸ TargetSheetLift.vertexPoint
        diagram root target level.object level.rootVertex initial
          decoded.1.1) =
    TargetSheetLift.branchCarrierEquiv diagram root target branch
      (TargetSheetLift.edgePoint diagram root target level.object
        level.rootVertex initial liftedEdge) at targetCompatibility
  have glueCancellation :
      (target.glue branch reference).hom.hom.hom
          (TargetSheetLift.branchCarrierEquiv diagram root target branch
            (TargetSheetLift.edgePoint diagram root target level.object
              level.rootVertex initial liftedEdge)) =
        TargetSheetLift.edgePoint diagram root target level.object
          level.rootVertex initial liftedEdge := by
    unfold TargetSheetLift.branchCarrierEquiv
    unfold SourceFiniteLevelUniversalCover.actionCarrierEquiv
    rw [← glue_inv_eq_reverse_hom diagram target reference branch]
    exact ConcreteCategory.congr_hom
      (target.glue reference branch).hom_inv_id
      (TargetSheetLift.edgePoint diagram root target level.object
        level.rootVertex initial liftedEdge)
  change (edgeHom diagram root level target split initial
      liftedEdge.edge.1).hom.hom basePoint =
    (target.glue branch reference).hom.hom.hom
      ((vertexHom diagram root level target split initial
        branch.vertex).hom.hom pulled)
  calc
    (edgeHom diagram root level target split initial
        liftedEdge.edge.1).hom.hom basePoint =
      TargetSheetLift.edgePoint diagram root target level.object
        level.rootVertex initial liftedEdge := by
          exact edgeHom_base diagram root level target split initial
            liftedEdge.edge.1 ⟨liftedEdge, rfl⟩
    _ = (target.glue branch reference).hom.hom.hom
        (TargetSheetLift.branchCarrierEquiv diagram root target branch
          (TargetSheetLift.edgePoint diagram root target level.object
            level.rootVertex initial liftedEdge)) := glueCancellation.symm
    _ = (target.glue branch reference).hom.hom.hom
        ((vertexHom diagram root level target split initial
          branch.vertex).hom.hom pulled) := congrArg _
      (targetCompatibility.symm.trans vertexEvaluation.symm)

/-- The vertex constituent maps commute with every pairwise source and target
gluing comparison. -/
theorem branchNaturality
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    ((SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex).glue first second).hom ≫
        second.temperoidPullback.map
          (vertexHom diagram root level target split initial second.vertex) =
      first.temperoidPullback.map
          (vertexHom diagram root level target split initial first.vertex) ≫
        (target.glue first second).hom := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  let firstBranchIso := SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
    diagram root level.object level.rootVertex first
  let secondBranchIso := SourceFiniteLevelUniversalCover.branchEdgeFamilyIso
    diagram root level.object level.rootVertex second
  let commonEdgeMap := edgeHom
    diagram root level target split initial edge
  let firstVertexMap := first.temperoidPullback.map
    (vertexHom diagram root level target split initial first.vertex)
  let secondVertexMap := second.temperoidPullback.map
    (vertexHom diagram root level target split initial second.vertex)
  let firstTargetGlue := (target.glue first reference).hom
  let secondTargetGlue := (target.glue second reference).hom
  let reverseSecondTargetGlue := (target.glue reference second).hom
  have firstHalf : commonEdgeMap =
      firstBranchIso.inv ≫ firstVertexMap ≫ firstTargetGlue := by
    simpa only [commonEdgeMap, firstBranchIso, firstVertexMap,
      firstTargetGlue] using
        branchHalfNaturality
          diagram root level target split initial first
  have secondHalf : commonEdgeMap =
      secondBranchIso.inv ≫ secondVertexMap ≫ secondTargetGlue := by
    simpa only [commonEdgeMap, secondBranchIso, secondVertexMap,
      secondTargetGlue] using
        branchHalfNaturality
          diagram root level target split initial second
  have secondFactor : secondBranchIso.inv ≫ secondVertexMap =
      commonEdgeMap ≫ reverseSecondTargetGlue := by
    rw [show reverseSecondTargetGlue =
        (target.glue second reference).inv by
      exact (glue_inv_eq_reverse_hom
        diagram target second reference).symm]
    have targetCancellation :
        commonEdgeMap ≫ (target.glue second reference).inv ≫
            (target.glue second reference).hom = commonEdgeMap := by
      calc
        commonEdgeMap ≫ (target.glue second reference).inv ≫
            (target.glue second reference).hom =
          commonEdgeMap ≫ ((target.glue second reference).inv ≫
            (target.glue second reference).hom) := rfl
        _ = commonEdgeMap ≫ 𝟙 _ := congrArg (commonEdgeMap ≫ ·)
          (target.glue second reference).inv_hom_id
        _ = commonEdgeMap := Category.comp_id _
    apply (cancel_mono secondTargetGlue).1
    change secondBranchIso.inv ≫ secondVertexMap ≫ secondTargetGlue =
      commonEdgeMap ≫ (target.glue second reference).inv ≫
        (target.glue second reference).hom
    rw [targetCancellation]
    exact secondHalf.symm
  have firstFactor : firstBranchIso.hom ≫ commonEdgeMap =
      firstVertexMap ≫ firstTargetGlue := by
    rw [firstHalf]
    change firstBranchIso.hom ≫ firstBranchIso.inv ≫
      firstVertexMap ≫ firstTargetGlue = firstVertexMap ≫ firstTargetGlue
    exact firstBranchIso.hom_inv_id_assoc
      (firstVertexMap ≫ firstTargetGlue)
  have targetGlueComposition :
      firstTargetGlue ≫ reverseSecondTargetGlue =
        (target.glue first second).hom := by
    exact congrArg Iso.hom (target.glue_trans first reference second)
  change (firstBranchIso.hom ≫ secondBranchIso.inv) ≫
      secondVertexMap = firstVertexMap ≫ (target.glue first second).hom
  calc
    (firstBranchIso.hom ≫ secondBranchIso.inv) ≫ secondVertexMap =
        firstBranchIso.hom ≫
          (secondBranchIso.inv ≫ secondVertexMap) := Category.assoc _ _ _
    _ = firstBranchIso.hom ≫
        (commonEdgeMap ≫ reverseSecondTargetGlue) :=
      congrArg (firstBranchIso.hom ≫ ·) secondFactor
    _ = (firstBranchIso.hom ≫ commonEdgeMap) ≫
        reverseSecondTargetGlue := (Category.assoc _ _ _).symm
    _ = (firstVertexMap ≫ firstTargetGlue) ≫
        reverseSecondTargetGlue :=
      congrArg (· ≫ reverseSecondTargetGlue) firstFactor
    _ = firstVertexMap ≫
        (firstTargetGlue ≫ reverseSecondTargetGlue) := Category.assoc _ _ _
    _ = firstVertexMap ≫ (target.glue first second).hom :=
      congrArg (firstVertexMap ≫ ·) targetGlueComposition

/-- A splitting pointed Galois level geometrically dominates the target:
the universal-cover constituents and their corrected local maps assemble into
a literal morphism in `B^cov(G)`. -/
noncomputable def hom
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex ⟶ target where
  app := vertexHom diagram root level target split initial
  naturality := branchNaturality
    diagram root level target split initial

end GeometricDomination

end SourceSemiGraphOfAnabelioids.CovObject

end Iut
