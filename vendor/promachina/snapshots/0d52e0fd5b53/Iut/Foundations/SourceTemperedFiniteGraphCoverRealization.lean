/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedGraphCoverRealization
import Iut.Foundations.SourceTemperedFiniteRecovery
import Iut.Foundations.SourceTemperedFiniteComponentComparison

/-!
# Realizing finite graph covers of a finite étale level

The universal graph cover of a finite étale level was realized geometrically
in `SourceTemperedGraphCoverRealization`.  The residual-finiteness argument of
Corollary 1.7 also needs its finite graph-cover quotients.  This file performs
that reindexing directly from the local bijectivity of a graph covering.

No geometric constituent is postulated: vertices and edges of the graph cover
select orbit components of the given finite étale level, and excision supplies
the unique incidence comparison used for the gluing.
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

namespace SourceSemiGraph.Hom

variable {source target : SourceSemiGraph.{u}}

/-- A graph covering identifies the branches incident to a source vertex with
the branches incident to its image. -/
noncomputable def incidentBranchEquiv (map : source.Hom target)
    (covering : map.IsGraphCovering) (vertex : source.Vertex) :
    source.IncidentBranch vertex ≃
      target.IncidentBranch (map.vertexMap vertex) :=
  Equiv.ofBijective (map.incidentBranchMap vertex) (covering.2 vertex)

@[simp]
theorem incidentBranchEquiv_apply (map : source.Hom target)
    (covering : map.IsGraphCovering) (vertex : source.Vertex)
    (branch : source.IncidentBranch vertex) :
    map.incidentBranchEquiv covering vertex branch =
      map.incidentBranchMap vertex branch :=
  rfl

/-- Once the source edge is fixed, the induced total-branch map is
injective, because its branch map is an equivalence. -/
theorem totalBranchMap_eq_of_edge_eq
    (map : source.Hom target)
    (first second : source.TotalBranch)
    (edgeEquality : first.1 = second.1)
    (mappedEquality : map.totalBranchMap first =
      map.totalBranchMap second) : first = second := by
  rcases first with ⟨firstEdge, firstBranch⟩
  rcases second with ⟨secondEdge, secondBranch⟩
  change firstEdge = secondEdge at edgeEquality
  cases edgeEquality
  have branchHEq := (Sigma.mk.inj_iff.mp mappedEquality).2
  have branchEquality :=
    (map.branchEquiv firstEdge).injective (eq_of_heq branchHEq)
  cases branchEquality
  rfl

end SourceSemiGraph.Hom

namespace SourceFiniteGraphCoverRealization

open SourceSemiGraphOfAnabelioids.GluedObject
open SourceSemiGraphOfAnabelioids.CovObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex) (object : diagram.GluedObject)

noncomputable abbrev LevelSemiGraph :=
  SourceFiniteLevelUniversalCover.LevelSemiGraph diagram root object

variable (cover : SourceSemiGraph.{u})
    (projection : cover.Hom (LevelSemiGraph diagram root object))
    (covering : projection.IsGraphCovering)

/-- Vertices of the graph cover lying over a fixed vertex of the original
semi-graph. -/
abbrev VertexIndex (vertex : diagram.base.Vertex) :=
  {lifted : cover.Vertex // (projection.vertexMap lifted).1 = vertex}

/-- Edges of the graph cover lying over a fixed edge of the original
semi-graph. -/
abbrev EdgeIndex (edge : diagram.base.Edge) :=
  {lifted : cover.Edge // (projection.edgeMap lifted).1 = edge}

instance vertexIndex_countable [Countable cover.Vertex]
    (vertex : diagram.base.Vertex) :
    Countable (VertexIndex diagram root object cover projection vertex) :=
  Function.Injective.countable Subtype.val_injective

instance edgeIndex_countable [Countable cover.Edge]
    (edge : diagram.base.Edge) :
    Countable (EdgeIndex diagram root object cover projection edge) :=
  Function.Injective.countable Subtype.val_injective

/-- The finite vertex-action component selected by a vertex of the graph
cover. -/
noncomputable def selectedVertexComponent (vertex : diagram.base.Vertex)
    (index : VertexIndex diagram root object cover projection vertex) :
    SourceActionComponent (diagram.vertexAnabelioid vertex).group
      ((diagram.vertexAnabelioid vertex).finiteAction
        (object.vertexObject vertex)) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact index.2 ▸
    finiteVertexComponentEquiv diagram root object
      (projection.vertexMap index.1).1 (projection.vertexMap index.1).2

/-- Repeat the selected finite orbit at every graph-cover vertex above a base
vertex. -/
noncomputable def vertexAction [Countable cover.Vertex]
    (vertex : diagram.base.Vertex) :
    SourceTemperoidAction (diagram.vertexAnabelioid vertex).group := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact sourceTemperoidComponentFamilyAction
    (diagram.vertexAnabelioid vertex).group
    ((diagram.vertexAnabelioid vertex).finiteAction
      (object.vertexObject vertex))
    (VertexIndex diagram root object cover projection vertex)
    (selectedVertexComponent diagram root object cover projection vertex)

/-- Components obtained by restricting the selected vertex families along a
fixed branch of the original semi-graph. -/
abbrev RestrictedBranchIndex
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :=
  SourceRestrictedComponentFamilyIndex
    (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
    ((diagram.vertexAnabelioid branch.vertex).finiteAction
      (object.vertexObject branch.vertex))
    (VertexIndex diagram root object cover projection branch.vertex)
    (selectedVertexComponent diagram root object cover projection branch.vertex)

/-- Decode the finite-level edge component carried by a restricted vertex
orbit. -/
noncomputable def restrictedFiniteEdgeComponent
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    CoverEdgeComponent diagram root object edge := by
  let reference := SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
    diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact
    (finiteCanonicalEdgeComponentEquiv diagram root object edge).symm
      (sourceFiniteActionComponentEquiv
        (finiteBranchActionIso diagram root object branch) index.2.1)

theorem restrictedFiniteEdgeComponent_incidence
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    finiteVertexComponentEquiv diagram root object branch.vertex
        (coverComponentMap diagram root object branch
          (restrictedFiniteEdgeComponent
            diagram root object cover projection branch index)) =
      selectedVertexComponent diagram root object cover projection branch.vertex
        index.1 := by
  let reference := SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
    diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  rw [← finiteBranchComponentCompatibility diagram root object branch
    (restrictedFiniteEdgeComponent
      diagram root object cover projection branch index)]
  unfold restrictedFiniteEdgeComponent
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact index.2.2

/-- The finite-level vertex encoded by a restricted component is precisely
the image of its graph-cover vertex. -/
theorem restrictedFiniteEdgeComponent_incidentVertex
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    (⟨branch.vertex,
      coverComponentMap diagram root object branch
        (restrictedFiniteEdgeComponent
          diagram root object cover projection branch index)⟩ :
        (LevelSemiGraph diagram root object).Vertex) =
      projection.vertexMap index.1.1 := by
  apply (SourceFiniteLevelUniversalCover.totalFiniteVertexComponentEquiv
    diagram root object).injective
  apply Sigma.ext index.1.2.symm
  exact (heq_of_eq (restrictedFiniteEdgeComponent_incidence
      diagram root object cover projection branch index)).trans
    (eqRec_heq index.1.2
      ((finiteVertexComponentEquiv diagram root object
        (projection.vertexMap index.1.1).1)
          (projection.vertexMap index.1.1).2))

/-- The target incident branch of the finite level represented by a
restricted component. -/
noncomputable def restrictedFiniteIncidentBranch
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    (LevelSemiGraph diagram root object).IncidentBranch
      (projection.vertexMap index.1.1) := by
  let component := restrictedFiniteEdgeComponent
    diagram root object cover projection branch index
  refine ⟨⟨⟨edge, component⟩, branch.branch⟩, ?_⟩
  change (finiteEtaleCoverSemiGraph diagram root object).coincidence
    ⟨edge, component⟩ branch.branch = some (projection.vertexMap index.1.1)
  rw [finiteEtaleCoverSemiGraph_coincidence_of_some
    diagram root object branch.abuts]
  exact congrArg some (restrictedFiniteEdgeComponent_incidentVertex
    diagram root object cover projection branch index)

/-- Lift the finite-level incidence uniquely through the graph covering. -/
noncomputable def restrictedSourceIncidentBranch
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    cover.IncidentBranch index.1.1 :=
  (projection.incidentBranchEquiv covering index.1.1).symm
    (restrictedFiniteIncidentBranch
      diagram root object cover projection branch index)

theorem restrictedSourceIncidentBranch_mapsTo
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    projection.incidentBranchMap index.1.1
        (restrictedSourceIncidentBranch
          diagram root object cover projection covering branch index) =
      restrictedFiniteIncidentBranch
        diagram root object cover projection branch index := by
  exact (projection.incidentBranchEquiv covering index.1.1).apply_symm_apply _

/-- A restricted vertex component determines the unique graph-cover edge
above the displayed base edge. -/
noncomputable def restrictedBranchIndexToEdgeIndex
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    RestrictedBranchIndex diagram root object cover projection branch →
      EdgeIndex diagram root object cover projection edge := fun index ↦ by
  let sourceBranch := restrictedSourceIncidentBranch
    diagram root object cover projection covering branch index
  refine ⟨sourceBranch.1.1, ?_⟩
  have mapped := congrArg
    (fun incident : (LevelSemiGraph diagram root object).IncidentBranch
        (projection.vertexMap index.1.1) ↦ incident.1.1.1)
    (restrictedSourceIncidentBranch_mapsTo
      diagram root object cover projection covering branch index)
  exact mapped

/-- Recover the restricted vertex component incident to a graph-cover edge.
The source vertex is forced by properness after pulling back the displayed
base branch through the branch equivalence. -/
noncomputable def liftedEdgeToRestrictedBranchIndex
    (liftedEdge : cover.Edge)
    (branch : diagram.IncidentBranch (projection.edgeMap liftedEdge).1) :
    RestrictedBranchIndex diagram root object cover projection branch := by
  let component := (projection.edgeMap liftedEdge).2
  let sourceBranch : cover.Branch liftedEdge :=
    (projection.branchEquiv liftedEdge).symm branch.branch
  have targetCoincidence :
      (LevelSemiGraph diagram root object).coincidence
          (projection.edgeMap liftedEdge)
          (projection.branchEquiv liftedEdge sourceBranch) =
        some ⟨branch.vertex,
          coverComponentMap diagram root object branch component⟩ := by
    simpa only [sourceBranch, Equiv.apply_symm_apply] using
      (finiteEtaleCoverSemiGraph_coincidence_of_some
        diagram root object branch.abuts)
  have sourceVerticial : ∃ vertex,
      cover.coincidence liftedEdge sourceBranch = some vertex :=
    (covering.1 liftedEdge sourceBranch).mpr
      ⟨⟨branch.vertex,
        coverComponentMap diagram root object branch component⟩,
        targetCoincidence⟩
  let liftedVertex := Classical.choose sourceVerticial
  have sourceCoincidence :
      cover.coincidence liftedEdge sourceBranch = some liftedVertex :=
    Classical.choose_spec sourceVerticial
  have mappedCoincidence := projection.map_coincidence
    liftedEdge sourceBranch liftedVertex sourceCoincidence
  have imageVertex : projection.vertexMap liftedVertex =
      (⟨branch.vertex,
        coverComponentMap diagram root object branch component⟩ :
          (LevelSemiGraph diagram root object).Vertex) := by
    apply Option.some.inj
    have mappedCoincidence' :
        (LevelSemiGraph diagram root object).coincidence
            (projection.edgeMap liftedEdge)
            (projection.branchEquiv liftedEdge sourceBranch) =
          some (projection.vertexMap liftedVertex) := by
      simpa only [sourceBranch, Equiv.apply_symm_apply] using mappedCoincidence
    exact mappedCoincidence'.symm.trans targetCoincidence
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root (projection.edgeMap liftedEdge).1
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid
    (projection.edgeMap liftedEdge).1).coverCategory
  let restrictedComponent :=
    (sourceFiniteActionComponentEquiv
      (finiteBranchActionIso diagram root object branch)).symm
        (finiteCanonicalEdgeComponentEquiv diagram root object
          (projection.edgeMap liftedEdge).1 component)
  let baseEquality : (projection.vertexMap liftedVertex).1 = branch.vertex :=
    congrArg Sigma.fst imageVertex
  refine ⟨⟨liftedVertex, baseEquality⟩, ⟨restrictedComponent, ?_⟩⟩
  have compatibility := finiteBranchComponentCompatibility
    diagram root object branch component
  rw [show sourceFiniteRestrictionComponentMap
      (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
      ((diagram.vertexAnabelioid branch.vertex).finiteAction
        (object.vertexObject branch.vertex)) restrictedComponent =
    finiteVertexComponentEquiv diagram root object branch.vertex
      (coverComponentMap diagram root object branch component) by
        simpa only [restrictedComponent] using compatibility]
  unfold selectedVertexComponent
  let totalEquiv :=
    SourceFiniteLevelUniversalCover.totalFiniteVertexComponentEquiv
      diagram root object
  have selectedSigma := congrArg totalEquiv imageVertex
  have componentHEq : HEq
      (finiteVertexComponentEquiv diagram root object
        (projection.vertexMap liftedVertex).1
          (projection.vertexMap liftedVertex).2)
      (finiteVertexComponentEquiv diagram root object branch.vertex
        (coverComponentMap diagram root object branch component)) :=
    (Sigma.mk.inj_iff.mp selectedSigma).2
  exact eq_of_heq <| ((eqRec_heq baseEquality
    (finiteVertexComponentEquiv diagram root object
      (projection.vertexMap liftedVertex).1
        (projection.vertexMap liftedVertex).2)).trans componentHEq).symm

/-- Recover a restricted branch index when the underlying base edge is only
specified propositionally. -/
noncomputable def edgeIndexToRestrictedBranchIndex
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    EdgeIndex diagram root object cover projection edge →
      RestrictedBranchIndex diagram root object cover projection branch
  | ⟨liftedEdge, edgeEquality⟩ => by
      cases edgeEquality
      exact liftedEdgeToRestrictedBranchIndex
        diagram root object cover projection covering liftedEdge branch

@[simp]
theorem edgeIndexToRestrictedBranchIndex_refl
    (liftedEdge : cover.Edge)
    (branch : diagram.IncidentBranch (projection.edgeMap liftedEdge).1) :
    edgeIndexToRestrictedBranchIndex
        diagram root object cover projection covering branch
          ⟨liftedEdge, rfl⟩ =
      liftedEdgeToRestrictedBranchIndex
        diagram root object cover projection covering liftedEdge branch :=
  rfl

/-- Decoding a graph-cover edge recovers the finite edge component stored in
its image at the chosen finite level. -/
theorem restrictedFiniteEdgeComponent_edgeIndexToRestricted
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : EdgeIndex diagram root object cover projection edge) :
    restrictedFiniteEdgeComponent diagram root object cover projection branch
        (edgeIndexToRestrictedBranchIndex
          diagram root object cover projection covering branch index) =
      index.2 ▸ (projection.edgeMap index.1).2 := by
  rcases index with ⟨liftedEdge, edgeEquality⟩
  cases edgeEquality
  rw [edgeIndexToRestrictedBranchIndex_refl]
  unfold liftedEdgeToRestrictedBranchIndex
  unfold restrictedFiniteEdgeComponent
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Encoding after decoding returns the original graph-cover edge. -/
theorem restrictedBranchIndexToEdgeIndex_rightInverse
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    Function.RightInverse
      (edgeIndexToRestrictedBranchIndex
        diagram root object cover projection covering branch)
      (restrictedBranchIndexToEdgeIndex
        diagram root object cover projection covering branch) := by
  rintro ⟨liftedEdge, edgeEquality⟩
  cases edgeEquality
  apply Subtype.ext
  rw [edgeIndexToRestrictedBranchIndex_refl]
  let decoded := liftedEdgeToRestrictedBranchIndex
    diagram root object cover projection covering liftedEdge branch
  let sourceBranch : cover.Branch liftedEdge :=
    (projection.branchEquiv liftedEdge).symm branch.branch
  have sourceVerticial : ∃ vertex,
      cover.coincidence liftedEdge sourceBranch = some vertex := by
    apply (covering.1 liftedEdge sourceBranch).mpr
    refine ⟨⟨branch.vertex,
      coverComponentMap diagram root object branch
        (projection.edgeMap liftedEdge).2⟩, ?_⟩
    simpa only [sourceBranch, Equiv.apply_symm_apply] using
      (finiteEtaleCoverSemiGraph_coincidence_of_some
        diagram root object branch.abuts)
  let liftedVertex := Classical.choose sourceVerticial
  have sourceCoincidence :
      cover.coincidence liftedEdge sourceBranch = some liftedVertex :=
    Classical.choose_spec sourceVerticial
  let liftedBranch : cover.IncidentBranch liftedVertex :=
    ⟨⟨liftedEdge, sourceBranch⟩, sourceCoincidence⟩
  have incidentEquality :
      restrictedFiniteIncidentBranch
          diagram root object cover projection branch decoded =
        projection.incidentBranchMap liftedVertex liftedBranch := by
    apply Subtype.ext
    change (⟨⟨(projection.edgeMap liftedEdge).1,
          restrictedFiniteEdgeComponent
            diagram root object cover projection branch decoded⟩,
          branch.branch⟩ :
        (LevelSemiGraph diagram root object).TotalBranch) =
      ⟨projection.edgeMap liftedEdge,
        projection.branchEquiv liftedEdge sourceBranch⟩
    apply Sigma.ext
    · exact Sigma.ext rfl <| heq_of_eq
        (restrictedFiniteEdgeComponent_edgeIndexToRestricted
          diagram root object cover projection covering branch
            ⟨liftedEdge, rfl⟩)
    · simp only [sourceBranch, Equiv.apply_symm_apply]
      exact HEq.rfl
  have sourceIncidentEquality :
      restrictedSourceIncidentBranch
          diagram root object cover projection covering branch decoded =
        liftedBranch := by
    change (projection.incidentBranchEquiv covering liftedVertex).symm
        (restrictedFiniteIncidentBranch
          diagram root object cover projection branch decoded) = liftedBranch
    rw [incidentEquality]
    change (projection.incidentBranchEquiv covering liftedVertex).symm
        ((projection.incidentBranchEquiv covering liftedVertex) liftedBranch) =
      liftedBranch
    exact (projection.incidentBranchEquiv covering liftedVertex).symm_apply_apply _
  exact congrArg (fun incident : cover.IncidentBranch liftedVertex ↦
    incident.1.1) sourceIncidentEquality

/-- Restricted indices are determined by their source vertex and restricted
finite-action component; all other fields are propositions. -/
theorem restrictedBranchIndex_encoding_injective
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    Function.Injective (fun index :
      RestrictedBranchIndex diagram root object cover projection branch ↦
        (index.1.1, index.2.1)) := by
  rintro ⟨⟨firstVertex, firstBase⟩,
      ⟨firstComponent, firstCompatibility⟩⟩
    ⟨⟨secondVertex, secondBase⟩,
      ⟨secondComponent, secondCompatibility⟩⟩ equality
  have vertexEquality : firstVertex = secondVertex :=
    congrArg Prod.fst equality
  have componentEquality : firstComponent = secondComponent :=
    congrArg Prod.snd equality
  cases vertexEquality
  cases componentEquality
  rfl

/-- The graph-cover edge remembers both the incident source vertex and the
restricted finite orbit, so the reindexing map is injective. -/
theorem restrictedBranchIndexToEdgeIndex_injective
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    Function.Injective
      (restrictedBranchIndexToEdgeIndex
        diagram root object cover projection covering branch) := by
  intro first second equality
  let firstIncident := restrictedSourceIncidentBranch
    diagram root object cover projection covering branch first
  let secondIncident := restrictedSourceIncidentBranch
    diagram root object cover projection covering branch second
  have sourceEdgeEquality : firstIncident.1.1 = secondIncident.1.1 :=
    congrArg Subtype.val equality
  have firstMapped := restrictedSourceIncidentBranch_mapsTo
    diagram root object cover projection covering branch first
  have secondMapped := restrictedSourceIncidentBranch_mapsTo
    diagram root object cover projection covering branch second
  have firstTotalMapped := congrArg Subtype.val firstMapped
  have secondTotalMapped := congrArg Subtype.val secondMapped
  have targetEdgeEquality :
      (⟨edge, restrictedFiniteEdgeComponent
        diagram root object cover projection branch first⟩ :
          (LevelSemiGraph diagram root object).Edge) =
        ⟨edge, restrictedFiniteEdgeComponent
          diagram root object cover projection branch second⟩ := by
    have mappedEdgeEquality :
        projection.edgeMap firstIncident.1.1 =
          projection.edgeMap secondIncident.1.1 :=
      congrArg projection.edgeMap sourceEdgeEquality
    have firstEdgeMapped := congrArg Sigma.fst firstTotalMapped
    have secondEdgeMapped := congrArg Sigma.fst secondTotalMapped
    exact firstEdgeMapped.symm.trans
      (mappedEdgeEquality.trans secondEdgeMapped)
  have targetTotalEquality :
      (restrictedFiniteIncidentBranch
        diagram root object cover projection branch first).1 =
      (restrictedFiniteIncidentBranch
        diagram root object cover projection branch second).1 := by
    apply Sigma.ext targetEdgeEquality
    exact HEq.rfl
  have sourceTotalEquality : firstIncident.1 = secondIncident.1 :=
    SourceSemiGraph.Hom.totalBranchMap_eq_of_edge_eq projection
      firstIncident.1 secondIncident.1 sourceEdgeEquality
      (firstTotalMapped.trans
        (targetTotalEquality.trans secondTotalMapped.symm))
  have sourceVertexEquality : first.1.1 = second.1.1 := by
    have coincidenceEquality := congrArg cover.coincidenceTotal sourceTotalEquality
    exact Option.some.inj (firstIncident.2.symm.trans
      (coincidenceEquality.trans secondIncident.2))
  have finiteComponentEquality :
      restrictedFiniteEdgeComponent
          diagram root object cover projection branch first =
        restrictedFiniteEdgeComponent
          diagram root object cover projection branch second := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp targetEdgeEquality).2
  have restrictedComponentEquality : first.2.1 = second.2.1 := by
    let reference :=
      SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    have mapped := congrArg
      (finiteCanonicalEdgeComponentEquiv diagram root object edge)
      finiteComponentEquality
    have actionComponentEquality :
        sourceFiniteActionComponentEquiv
            (finiteBranchActionIso diagram root object branch) first.2.1 =
          sourceFiniteActionComponentEquiv
            (finiteBranchActionIso diagram root object branch) second.2.1 := by
      simpa only [restrictedFiniteEdgeComponent,
        Equiv.apply_symm_apply] using mapped
    exact (sourceFiniteActionComponentEquiv
      (finiteBranchActionIso diagram root object branch)).injective
        actionComponentEquality
  apply restrictedBranchIndex_encoding_injective
    diagram root object cover projection branch
  exact Prod.ext sourceVertexEquality restrictedComponentEquality

/-- Decoding after encoding returns the original restricted component. -/
theorem restrictedBranchIndexToEdgeIndex_leftInverse
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    Function.LeftInverse
      (edgeIndexToRestrictedBranchIndex
        diagram root object cover projection covering branch)
      (restrictedBranchIndexToEdgeIndex
        diagram root object cover projection covering branch) := by
  intro index
  apply restrictedBranchIndexToEdgeIndex_injective
    diagram root object cover projection covering branch
  exact restrictedBranchIndexToEdgeIndex_rightInverse
    diagram root object cover projection covering branch
      (restrictedBranchIndexToEdgeIndex
        diagram root object cover projection covering branch index)

/-- Local incidence reindexes the restricted orbit family by the common
family of graph-cover edges. -/
noncomputable def restrictedBranchIndexEquivEdgeIndex
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    RestrictedBranchIndex diagram root object cover projection branch ≃
      EdgeIndex diagram root object cover projection edge where
  toFun := restrictedBranchIndexToEdgeIndex
    diagram root object cover projection covering branch
  invFun := edgeIndexToRestrictedBranchIndex
    diagram root object cover projection covering branch
  left_inv := restrictedBranchIndexToEdgeIndex_leftInverse
    diagram root object cover projection covering branch
  right_inv := restrictedBranchIndexToEdgeIndex_rightInverse
    diagram root object cover projection covering branch

/-- The finite edge-action component selected by an edge of the graph cover. -/
noncomputable def selectedEdgeComponent (edge : diagram.base.Edge)
    (index : EdgeIndex diagram root object cover projection edge) :
    SourceActionComponent (diagram.edgeAnabelioid edge).group
      ((diagram.edgeAnabelioid edge).finiteAction
        (coverEdgeObject diagram root object edge)) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact index.2 ▸ finiteCanonicalEdgeComponentEquiv
    diagram root object (projection.edgeMap index.1).1
      (projection.edgeMap index.1).2

/-- Componentwise finite edge comparison, retaining the base-edge index. -/
noncomputable def totalFiniteEdgeComponentEquiv :
    (LevelSemiGraph diagram root object).Edge ≃
      Σ edge : diagram.base.Edge,
        SourceActionComponent (diagram.edgeAnabelioid edge).group
          ((diagram.edgeAnabelioid edge).finiteAction
            (coverEdgeObject diagram root object edge)) := by
  letI (edge : diagram.base.Edge) :=
    (diagram.vertexAnabelioid
      (SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge).vertex).coverCategory
  letI (edge : diagram.base.Edge) :=
    (diagram.edgeAnabelioid edge).coverCategory
  exact Equiv.sigmaCongrRight
    (fun edge ↦ finiteCanonicalEdgeComponentEquiv diagram root object edge)

/-- For an edge produced from a restricted branch index, the selected edge
component is exactly the component decoded from that index. -/
theorem selectedEdgeComponent_restricted
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    letI := (diagram.vertexAnabelioid
      (SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    selectedEdgeComponent diagram root object cover projection edge
        (restrictedBranchIndexToEdgeIndex
          diagram root object cover projection covering branch index) =
      finiteCanonicalEdgeComponentEquiv diagram root object edge
        (restrictedFiniteEdgeComponent
          diagram root object cover projection branch index) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  let output := restrictedBranchIndexToEdgeIndex
    diagram root object cover projection covering branch index
  let sourceIncident := restrictedSourceIncidentBranch
    diagram root object cover projection covering branch index
  have imageEdge : projection.edgeMap output.1 =
      (⟨edge, restrictedFiniteEdgeComponent
        diagram root object cover projection branch index⟩ :
          (LevelSemiGraph diagram root object).Edge) :=
    by
      change projection.edgeMap sourceIncident.1.1 = _
      exact congrArg
        (fun incident : (LevelSemiGraph diagram root object).IncidentBranch
          (projection.vertexMap index.1.1) ↦ incident.1.1)
        (restrictedSourceIncidentBranch_mapsTo
          diagram root object cover projection covering branch index)
  let baseEquality : (projection.edgeMap output.1).1 = edge :=
    congrArg Sigma.fst imageEdge
  change selectedEdgeComponent diagram root object cover projection edge output = _
  unfold selectedEdgeComponent
  let totalEquiv := totalFiniteEdgeComponentEquiv diagram root object
  have selectedSigma := congrArg totalEquiv imageEdge
  have componentHEq : HEq
      (finiteCanonicalEdgeComponentEquiv diagram root object
        (projection.edgeMap output.1).1
          (projection.edgeMap output.1).2)
      (finiteCanonicalEdgeComponentEquiv diagram root object edge
        (restrictedFiniteEdgeComponent
          diagram root object cover projection branch index)) :=
    (Sigma.mk.inj_iff.mp selectedSigma).2
  have proofEquality : output.2 = baseEquality := Subsingleton.elim _ _
  change output.2 ▸
      finiteCanonicalEdgeComponentEquiv diagram root object
        (projection.edgeMap output.1).1
          (projection.edgeMap output.1).2 = _
  rw [proofEquality]
  exact eq_of_heq (rec_heq_of_heq
    (C := fun targetEdge : diagram.base.Edge ↦
      SourceActionComponent (diagram.edgeAnabelioid targetEdge).group
        ((diagram.edgeAnabelioid targetEdge).finiteAction
          (coverEdgeObject diagram root object targetEdge)))
    (x := finiteCanonicalEdgeComponentEquiv diagram root object
      (projection.edgeMap output.1).1 (projection.edgeMap output.1).2)
    (y := finiteCanonicalEdgeComponentEquiv diagram root object edge
      (restrictedFiniteEdgeComponent
        diagram root object cover projection branch index))
    baseEquality componentHEq)

theorem branchComponentCompatibility
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    sourceFiniteActionComponentEquiv
        (finiteBranchActionIso diagram root object branch) index.2.1 =
      selectedEdgeComponent diagram root object cover projection edge
        (restrictedBranchIndexEquivEdgeIndex
          diagram root object cover projection covering branch index) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  unfold restrictedBranchIndexEquivEdgeIndex
  change sourceFiniteActionComponentEquiv
      (finiteBranchActionIso diagram root object branch) index.2.1 =
    selectedEdgeComponent diagram root object cover projection edge
      (restrictedBranchIndexToEdgeIndex
        diagram root object cover projection covering branch index)
  rw [selectedEdgeComponent_restricted
    diagram root object cover projection covering branch index]
  unfold restrictedFiniteEdgeComponent
  rw [Equiv.apply_symm_apply]

/-- Repeat the selected finite edge orbit at every graph-cover edge above the
base edge. -/
noncomputable def edgeAction [Countable cover.Edge]
    (edge : diagram.base.Edge) :
    SourceTemperoidAction (diagram.edgeAnabelioid edge).group := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact sourceTemperoidComponentFamilyAction
    (diagram.edgeAnabelioid edge).group
    ((diagram.edgeAnabelioid edge).finiteAction
      (coverEdgeObject diagram root object edge))
    (EdgeIndex diagram root object cover projection edge)
    (selectedEdgeComponent diagram root object cover projection edge)

/-- Restriction of a vertex family along a branch is canonically the common
family of graph-cover edges. -/
noncomputable def branchEdgeFamilyIso
    [Countable cover.Vertex] [Countable cover.Edge]
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    branch.temperoidPullback.obj
        (vertexAction diagram root object cover projection branch.vertex) ≅
      edgeAction diagram root object cover projection edge := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact
    sourceRestrictedComponentFamilyActionIso
        (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
        ((diagram.vertexAnabelioid branch.vertex).finiteAction
          (object.vertexObject branch.vertex))
        (VertexIndex diagram root object cover projection branch.vertex)
        (selectedVertexComponent
          diagram root object cover projection branch.vertex) ≪≫
      sourceTemperoidComponentFamilyActionIso
        (finiteBranchActionIso diagram root object branch)
        (fun index : RestrictedBranchIndex
          diagram root object cover projection branch ↦ index.2.1)
        (selectedEdgeComponent diagram root object cover projection edge)
        (restrictedBranchIndexEquivEdgeIndex
          diagram root object cover projection covering branch)
        (branchComponentCompatibility
          diagram root object cover projection covering branch)

/-- The literal geometric cover obtained from the graph covering. -/
noncomputable def covObject
    [Countable cover.Vertex] [Countable cover.Edge] : diagram.CovObject where
  vertexObject := vertexAction diagram root object cover projection
  glue := fun first second ↦
    branchEdgeFamilyIso
        diagram root object cover projection covering first ≪≫
      (branchEdgeFamilyIso
        diagram root object cover projection covering second).symm
  glue_refl := by
    intro edge branch
    simp
  glue_trans := by
    intro edge first second third
    simp

/-- Forgetting a realized graph-cover index commutes with the branch-to-edge
identification. -/
theorem branchEdgeFamilyIso_projection
    [Countable cover.Vertex] [Countable cover.Edge]
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    let edgeProjection := sourceTemperoidComponentFamilyProjection
      (diagram.edgeAnabelioid edge).group
      ((diagram.edgeAnabelioid edge).finiteAction
        (coverEdgeObject diagram root object edge))
      (EdgeIndex diagram root object cover projection edge)
      (selectedEdgeComponent diagram root object cover projection edge)
    (branchEdgeFamilyIso diagram root object cover projection covering
          branch).hom ≫ edgeProjection =
      branch.temperoidPullback.map
          (sourceTemperoidComponentFamilyProjection
            (diagram.vertexAnabelioid branch.vertex).group
            ((diagram.vertexAnabelioid branch.vertex).finiteAction
              (object.vertexObject branch.vertex))
            (VertexIndex diagram root object cover projection branch.vertex)
            (selectedVertexComponent
              diagram root object cover projection branch.vertex)) ≫
        (finiteEdgeIdentification diagram root object branch).hom := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  let edgeProjection := sourceTemperoidComponentFamilyProjection
    (diagram.edgeAnabelioid edge).group
    ((diagram.edgeAnabelioid edge).finiteAction
      (coverEdgeObject diagram root object edge))
    (EdgeIndex diagram root object cover projection edge)
    (selectedEdgeComponent diagram root object cover projection edge)
  let restrictionIso := sourceRestrictedComponentFamilyActionIso
    (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
    ((diagram.vertexAnabelioid branch.vertex).finiteAction
      (object.vertexObject branch.vertex))
    (VertexIndex diagram root object cover projection branch.vertex)
    (selectedVertexComponent
      diagram root object cover projection branch.vertex)
  let reindexIso := sourceTemperoidComponentFamilyActionIso
    (finiteBranchActionIso diagram root object branch)
    (fun index : RestrictedBranchIndex
      diagram root object cover projection branch => index.2.1)
    (selectedEdgeComponent diagram root object cover projection edge)
    (restrictedBranchIndexEquivEdgeIndex
      diagram root object cover projection covering branch)
    (branchComponentCompatibility
      diagram root object cover projection covering branch)
  let restrictedProjection := sourceTemperoidComponentFamilyProjection
    (diagram.edgeAnabelioid edge).group
    (sourceFiniteRestrictionAction
      (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
      ((diagram.vertexAnabelioid branch.vertex).finiteAction
        (object.vertexObject branch.vertex)))
    (RestrictedBranchIndex diagram root object cover projection branch)
    (fun index => index.2.1)
  let vertexProjection := sourceTemperoidComponentFamilyProjection
    (diagram.vertexAnabelioid branch.vertex).group
    ((diagram.vertexAnabelioid branch.vertex).finiteAction
      (object.vertexObject branch.vertex))
    (VertexIndex diagram root object cover projection branch.vertex)
    (selectedVertexComponent
      diagram root object cover projection branch.vertex)
  have reindexNaturality :
      reindexIso.hom ≫ edgeProjection =
        restrictedProjection ≫
          (SourceTemperoidAction.finiteInclusion
            (diagram.edgeAnabelioid edge).group).map
              (finiteBranchActionIso
                diagram root object branch).hom := by
    exact sourceTemperoidComponentFamilyProjection_naturality
      (finiteBranchActionIso diagram root object branch)
      (fun index : RestrictedBranchIndex
        diagram root object cover projection branch => index.2.1)
      (selectedEdgeComponent diagram root object cover projection edge)
      (restrictedBranchIndexEquivEdgeIndex
        diagram root object cover projection covering branch)
      (branchComponentCompatibility
        diagram root object cover projection covering branch)
  have restrictionNaturality :
      restrictionIso.hom ≫ restrictedProjection =
        branch.temperoidPullback.map vertexProjection := by
    exact sourceRestrictedComponentFamilyProjection_naturality
      (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
      ((diagram.vertexAnabelioid branch.vertex).finiteAction
        (object.vertexObject branch.vertex))
      (VertexIndex diagram root object cover projection branch.vertex)
      (selectedVertexComponent
        diagram root object cover projection branch.vertex)
  change (restrictionIso.hom ≫ reindexIso.hom) ≫ edgeProjection =
    branch.temperoidPullback.map vertexProjection ≫
      (finiteEdgeIdentification diagram root object branch).hom
  have assembled :
      (restrictionIso.hom ≫ reindexIso.hom) ≫ edgeProjection =
        branch.temperoidPullback.map vertexProjection ≫
          (SourceTemperoidAction.finiteInclusion
            (diagram.edgeAnabelioid edge).group).map
              (finiteBranchActionIso diagram root object branch).hom := by
    calc
      (restrictionIso.hom ≫ reindexIso.hom) ≫ edgeProjection =
          restrictionIso.hom ≫ (reindexIso.hom ≫ edgeProjection) :=
        Category.assoc _ _ _
      _ = restrictionIso.hom ≫
          (restrictedProjection ≫
            (SourceTemperoidAction.finiteInclusion
              (diagram.edgeAnabelioid edge).group).map
                (finiteBranchActionIso diagram root object branch).hom) :=
        congrArg (fun map => restrictionIso.hom ≫ map) reindexNaturality
      _ = (restrictionIso.hom ≫ restrictedProjection) ≫
            (SourceTemperoidAction.finiteInclusion
              (diagram.edgeAnabelioid edge).group).map
                (finiteBranchActionIso diagram root object branch).hom :=
        (Category.assoc _ _ _).symm
      _ = branch.temperoidPullback.map vertexProjection ≫
            (SourceTemperoidAction.finiteInclusion
              (diagram.edgeAnabelioid edge).group).map
                (finiteBranchActionIso diagram root object branch).hom :=
        congrArg (fun map => map ≫
          (SourceTemperoidAction.finiteInclusion
            (diagram.edgeAnabelioid edge).group).map
              (finiteBranchActionIso
                diagram root object branch).hom) restrictionNaturality
  rw [finiteInclusion_map_finiteBranchActionIso_hom] at assembled
  exact assembled

/-- Forget the graph-cover copy index at every vertex.  The resulting map is
the geometric projection from the realized graph cover to the finite object
whose component semigraph was covered. -/
noncomputable def covObjectProjection
    [Countable cover.Vertex] [Countable cover.Edge] :
    covObject diagram root object cover projection covering ⟶
      finiteCovObject diagram root object where
  app := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact sourceTemperoidComponentFamilyProjection
      (diagram.vertexAnabelioid vertex).group
      ((diagram.vertexAnabelioid vertex).finiteAction
        (object.vertexObject vertex))
      (VertexIndex diagram root object cover projection vertex)
      (selectedVertexComponent
        diagram root object cover projection vertex)
  naturality := by
    intro edge first second
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    let edgeProjection := sourceTemperoidComponentFamilyProjection
      (diagram.edgeAnabelioid edge).group
      ((diagram.edgeAnabelioid edge).finiteAction
        (coverEdgeObject diagram root object edge))
      (EdgeIndex diagram root object cover projection edge)
      (selectedEdgeComponent diagram root object cover projection edge)
    have inverseBranchProjection :
        (branchEdgeFamilyIso diagram root object cover projection covering
              second).inv ≫
            second.temperoidPullback.map
              (sourceTemperoidComponentFamilyProjection
                (diagram.vertexAnabelioid second.vertex).group
                ((diagram.vertexAnabelioid second.vertex).finiteAction
                  (object.vertexObject second.vertex))
                (VertexIndex diagram root object cover projection second.vertex)
                (selectedVertexComponent diagram root object cover projection
                  second.vertex)) =
          edgeProjection ≫
            (finiteEdgeIdentification diagram root object second).inv := by
      apply (cancel_epi (branchEdgeFamilyIso diagram root object cover
        projection covering second).hom).1
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      symm
      have assembled :
          (branchEdgeFamilyIso diagram root object cover projection covering
                second).hom ≫
              (edgeProjection ≫
                (finiteEdgeIdentification diagram root object second).inv) =
            (second.temperoidPullback.map
                (sourceTemperoidComponentFamilyProjection
                  (diagram.vertexAnabelioid second.vertex).group
                  ((diagram.vertexAnabelioid second.vertex).finiteAction
                    (object.vertexObject second.vertex))
                  (VertexIndex diagram root object cover projection second.vertex)
                  (selectedVertexComponent diagram root object cover projection
                    second.vertex)) ≫
                (finiteEdgeIdentification diagram root object second).hom) ≫
              (finiteEdgeIdentification diagram root object second).inv := by
        calc
        (branchEdgeFamilyIso diagram root object cover projection covering
              second).hom ≫
            (edgeProjection ≫
              (finiteEdgeIdentification diagram root object second).inv) =
          ((branchEdgeFamilyIso diagram root object cover projection covering
              second).hom ≫ edgeProjection) ≫
                (finiteEdgeIdentification diagram root object second).inv :=
          (Category.assoc _ _ _).symm
        _ = (second.temperoidPullback.map
              (sourceTemperoidComponentFamilyProjection
                (diagram.vertexAnabelioid second.vertex).group
                ((diagram.vertexAnabelioid second.vertex).finiteAction
                  (object.vertexObject second.vertex))
                (VertexIndex diagram root object cover projection second.vertex)
                (selectedVertexComponent diagram root object cover projection
                  second.vertex)) ≫
              (finiteEdgeIdentification diagram root object second).hom) ≫
                (finiteEdgeIdentification diagram root object second).inv :=
          congrArg (fun map => map ≫
            (finiteEdgeIdentification diagram root object second).inv)
              (branchEdgeFamilyIso_projection
                diagram root object cover projection covering second)
      have cancelled :
          (second.temperoidPullback.map
                (sourceTemperoidComponentFamilyProjection
                  (diagram.vertexAnabelioid second.vertex).group
                  ((diagram.vertexAnabelioid second.vertex).finiteAction
                    (object.vertexObject second.vertex))
                  (VertexIndex diagram root object cover projection second.vertex)
                  (selectedVertexComponent diagram root object cover projection
                    second.vertex)) ≫
                (finiteEdgeIdentification diagram root object second).hom) ≫
              (finiteEdgeIdentification diagram root object second).inv =
            second.temperoidPullback.map
              (sourceTemperoidComponentFamilyProjection
                (diagram.vertexAnabelioid second.vertex).group
                ((diagram.vertexAnabelioid second.vertex).finiteAction
                  (object.vertexObject second.vertex))
                (VertexIndex diagram root object cover projection second.vertex)
                (selectedVertexComponent diagram root object cover projection
                  second.vertex)) := by
        exact (Iso.comp_inv_eq
          (finiteEdgeIdentification diagram root object second)).2 rfl
      exact assembled.trans cancelled
    change
      ((branchEdgeFamilyIso diagram root object cover projection covering
          first).hom ≫
        (branchEdgeFamilyIso diagram root object cover projection covering
          second).inv) ≫
          second.temperoidPullback.map
            (sourceTemperoidComponentFamilyProjection
              (diagram.vertexAnabelioid second.vertex).group
              ((diagram.vertexAnabelioid second.vertex).finiteAction
                (object.vertexObject second.vertex))
              (VertexIndex diagram root object cover projection second.vertex)
              (selectedVertexComponent
                diagram root object cover projection second.vertex)) =
        first.temperoidPullback.map
            (sourceTemperoidComponentFamilyProjection
              (diagram.vertexAnabelioid first.vertex).group
              ((diagram.vertexAnabelioid first.vertex).finiteAction
                (object.vertexObject first.vertex))
              (VertexIndex diagram root object cover projection first.vertex)
              (selectedVertexComponent
                diagram root object cover projection first.vertex)) ≫
          (finiteEdgeIdentification diagram root object first).hom ≫
            (finiteEdgeIdentification diagram root object second).inv
    rw [Category.assoc, inverseBranchProjection]
    calc
      (branchEdgeFamilyIso diagram root object cover projection covering
            first).hom ≫
          (edgeProjection ≫
            (finiteEdgeIdentification diagram root object second).inv) =
        ((branchEdgeFamilyIso diagram root object cover projection covering
            first).hom ≫ edgeProjection) ≫
              (finiteEdgeIdentification diagram root object second).inv :=
        (Category.assoc _ _ _).symm
      _ = (first.temperoidPullback.map
            (sourceTemperoidComponentFamilyProjection
              (diagram.vertexAnabelioid first.vertex).group
              ((diagram.vertexAnabelioid first.vertex).finiteAction
                (object.vertexObject first.vertex))
              (VertexIndex diagram root object cover projection first.vertex)
              (selectedVertexComponent
                diagram root object cover projection first.vertex)) ≫
            (finiteEdgeIdentification diagram root object first).hom) ≫
              (finiteEdgeIdentification diagram root object second).inv :=
        congrArg (fun map => map ≫
          (finiteEdgeIdentification diagram root object second).inv)
            (branchEdgeFamilyIso_projection
              diagram root object cover projection covering first)
      _ = first.temperoidPullback.map
            (sourceTemperoidComponentFamilyProjection
              (diagram.vertexAnabelioid first.vertex).group
              ((diagram.vertexAnabelioid first.vertex).finiteAction
                (object.vertexObject first.vertex))
              (VertexIndex diagram root object cover projection first.vertex)
              (selectedVertexComponent
                diagram root object cover projection first.vertex)) ≫
            (finiteEdgeIdentification diagram root object first).hom ≫
              (finiteEdgeIdentification diagram root object second).inv :=
        Category.assoc _ _ _

/-- Components of a vertex constituent are exactly graph-cover vertices in
the corresponding base fiber. -/
noncomputable def vertexComponentEquiv
    [Countable cover.Vertex] [Countable cover.Edge]
    (vertex : diagram.base.Vertex) :
    CoverVertexComponent diagram
        (covObject diagram root object cover projection covering) vertex ≃
      VertexIndex diagram root object cover projection vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact SourceTemperoidComponentFamilyAction.componentEquiv
    (diagram.vertexAnabelioid vertex).group
    ((diagram.vertexAnabelioid vertex).finiteAction
      (object.vertexObject vertex))
    (VertexIndex diagram root object cover projection vertex)
    (selectedVertexComponent diagram root object cover projection vertex)

/-- Components of the representative edge constituent are exactly
graph-cover edges in the corresponding base fiber. -/
noncomputable def edgeComponentEquiv
    [Countable cover.Vertex] [Countable cover.Edge]
    (edge : diagram.base.Edge) :
    CoverEdgeComponent diagram root
        (covObject diagram root object cover projection covering) edge ≃
      EdgeIndex diagram root object cover projection edge := by
  let reference :=
    SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact (actionComponentEquiv
    (branchEdgeFamilyIso
      diagram root object cover projection covering reference)).trans
      (SourceTemperoidComponentFamilyAction.componentEquiv
        (diagram.edgeAnabelioid edge).group
        ((diagram.edgeAnabelioid edge).finiteAction
          (coverEdgeObject diagram root object edge))
        (EdgeIndex diagram root object cover projection edge)
        (selectedEdgeComponent diagram root object cover projection edge))

/-- The finite level that supplied the orbit components splits the realized
graph cover, hence the result is tempered. -/
theorem covObject_isTempered
    [Countable cover.Vertex] [Countable cover.Edge] :
    IsTempered diagram root
      (covObject diagram root object cover projection covering) := by
  apply isTempered_of_isSplitBy diagram root (splitter := object)
  constructor
  · intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact SourceFiniteLevelUniversalCover.finiteActionKernelFixesComponentFamily
      (diagram.vertexAnabelioid vertex).group
      ((diagram.vertexAnabelioid vertex).finiteAction
        (object.vertexObject vertex))
      (VertexIndex diagram root object cover projection vertex)
      (selectedVertexComponent diagram root object cover projection vertex)
  · intro edge
    let reference :=
      SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    let canonicalFixes :=
      SourceFiniteLevelUniversalCover.finiteActionKernelFixesComponentFamily
        (diagram.edgeAnabelioid edge).group
        ((diagram.edgeAnabelioid edge).finiteAction
          (coverEdgeObject diagram root object edge))
        (EdgeIndex diagram root object cover projection edge)
        (selectedEdgeComponent diagram root object cover projection edge)
    exact SourceFiniteLevelUniversalCover.actionKernelFixes_transport
      (finiteEdgeIdentification diagram root object reference).symm
      (branchEdgeFamilyIso
        diagram root object cover projection covering reference).symm
      canonicalFixes

/-- Component incidence of the geometric object is the local graph-cover
incidence encoded by the branch-index equivalence. -/
theorem componentEquiv_incidence
    [Countable cover.Vertex] [Countable cover.Edge]
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (component : CoverEdgeComponent diagram root
      (covObject diagram root object cover projection covering) edge) :
    vertexComponentEquiv
        diagram root object cover projection covering branch.vertex
        (coverComponentMap diagram root
          (covObject diagram root object cover projection covering)
            branch component) =
      ((restrictedBranchIndexEquivEdgeIndex
        diagram root object cover projection covering branch).symm
          (edgeComponentEquiv
            diagram root object cover projection covering edge component)).1 := by
  induction component using Quotient.inductionOn' with
  | _ point => rfl

/-- Transport a base branch to the branch fiber of a graph-cover edge. -/
noncomputable def coverBranchEquiv
    {edge : diagram.base.Edge}
    (index : EdgeIndex diagram root object cover projection edge) :
    diagram.base.Branch edge ≃ cover.Branch index.1 :=
  (Equiv.cast (congrArg diagram.base.Branch index.2.symm)).trans
    (projection.branchEquiv index.1).symm

/-- Projecting a transported graph-cover branch returns the original base
branch, up to the dependent edge equality stored in the fiber index. -/
theorem coverBranchEquiv_projection_heq
    {edge : diagram.base.Edge}
    (index : EdgeIndex diagram root object cover projection edge)
    (branch : diagram.base.Branch edge) : HEq
    (projection.branchEquiv index.1
      (coverBranchEquiv diagram root object cover projection index branch))
    branch := by
  unfold coverBranchEquiv
  rw [Equiv.trans_apply]
  exact (heq_of_eq ((projection.branchEquiv index.1).apply_symm_apply
    ((Equiv.cast (congrArg diagram.base.Branch index.2.symm)) branch))).trans
      (cast_heq _ _)

/-- On an edge produced by local incidence, `coverBranchEquiv` returns the
same source branch that excision selected. -/
theorem coverBranchEquiv_restricted
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object cover projection branch) :
    coverBranchEquiv diagram root object cover projection
        (restrictedBranchIndexToEdgeIndex
          diagram root object cover projection covering branch index)
          branch.branch =
      (restrictedSourceIncidentBranch
        diagram root object cover projection covering branch index).1.2 := by
  let sourceIncident := restrictedSourceIncidentBranch
    diagram root object cover projection covering branch index
  apply (projection.branchEquiv sourceIncident.1.1).injective
  have mappedTotal := congrArg Subtype.val
    (restrictedSourceIncidentBranch_mapsTo
      diagram root object cover projection covering branch index)
  have mappedBranchHEq := (Sigma.mk.inj_iff.mp mappedTotal).2
  apply eq_of_heq
  exact (coverBranchEquiv_projection_heq
    diagram root object cover projection
      (restrictedBranchIndexToEdgeIndex
        diagram root object cover projection covering branch index)
      branch.branch).trans mappedBranchHEq.symm

/-- The graph-cover edge and branch decoded from an arbitrary edge fiber are
the canonical incident edge and branch of the decoded restricted index. -/
theorem coverBranchEquiv_edgeIndex
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : EdgeIndex diagram root object cover projection edge) :
    let decoded := (restrictedBranchIndexEquivEdgeIndex
      diagram root object cover projection covering branch).symm index
    (⟨index.1, coverBranchEquiv
      diagram root object cover projection index branch.branch⟩ :
        cover.TotalBranch) =
      (restrictedSourceIncidentBranch
        diagram root object cover projection covering branch decoded).1 := by
  let equivalence := restrictedBranchIndexEquivEdgeIndex
    diagram root object cover projection covering branch
  let decoded := equivalence.symm index
  have edgeEquality :
      restrictedBranchIndexToEdgeIndex
      diagram root object cover projection covering branch decoded = index :=
    equivalence.apply_symm_apply index
  rw [← edgeEquality]
  change (⟨(restrictedBranchIndexToEdgeIndex
      diagram root object cover projection covering branch decoded).1,
        coverBranchEquiv diagram root object cover projection
          (restrictedBranchIndexToEdgeIndex
            diagram root object cover projection covering branch decoded)
            branch.branch⟩ : cover.TotalBranch) =
    (restrictedSourceIncidentBranch
      diagram root object cover projection covering branch
        (equivalence.symm (equivalence decoded))).1
  rw [equivalence.symm_apply_apply]
  let sourceIncident := restrictedSourceIncidentBranch
    diagram root object cover projection covering branch decoded
  simpa only [restrictedBranchIndexToEdgeIndex, sourceIncident] using congrArg
    (fun liftedBranch : cover.Branch sourceIncident.1.1 ↦
      (⟨sourceIncident.1.1, liftedBranch⟩ : cover.TotalBranch))
    (coverBranchEquiv_restricted
      diagram root object cover projection covering branch decoded)

/-- The associated geometric component semigraph is canonically isomorphic
to the supplied graph cover. -/
noncomputable def coverComparison
    [Countable cover.Vertex] [Countable cover.Edge] :
    (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph diagram root
      (covObject diagram root object cover projection covering)).Hom cover where
  vertexMap := fun point ↦
    (vertexComponentEquiv
      diagram root object cover projection covering point.1 point.2).1
  edgeMap := fun point ↦
    (edgeComponentEquiv
      diagram root object cover projection covering point.1 point.2).1
  branchEquiv := fun point ↦ coverBranchEquiv
    diagram root object cover projection
      (edgeComponentEquiv
        diagram root object cover projection covering point.1 point.2)
  map_coincidence := by
    intro sourceEdge sourceBranch sourceVertex coincidence
    rcases sourceEdge with ⟨edge, edgeComponent⟩
    rcases sourceVertex with ⟨vertex, vertexComponent⟩
    change (match abuts : diagram.base.coincidence edge sourceBranch with
      | none => none
      | some target => some (⟨target,
          coverComponentMap diagram root
            (covObject diagram root object cover projection covering)
              ⟨sourceBranch, target, abuts⟩ edgeComponent⟩ :
            CoverVertex diagram
              (covObject diagram root object cover projection covering))) =
        some (⟨vertex, vertexComponent⟩ : CoverVertex diagram
          (covObject diagram root object cover projection covering))
      at coincidence
    split at coincidence
    next noVertex => cases coincidence
    next target abuts =>
      have vertexEquality : target = vertex :=
        Sigma.mk.inj_iff.mp (Option.some.inj coincidence) |>.1
      subst target
      have componentEquality :
          coverComponentMap diagram root
              (covObject diagram root object cover projection covering)
                ⟨sourceBranch, vertex, abuts⟩ edgeComponent =
            vertexComponent :=
        eq_of_heq (Sigma.mk.inj_iff.mp
          (Option.some.inj coincidence) |>.2)
      let edgeIndex := edgeComponentEquiv
        diagram root object cover projection covering edge edgeComponent
      let decoded := (restrictedBranchIndexEquivEdgeIndex
        diagram root object cover projection covering
          ⟨sourceBranch, vertex, abuts⟩).symm edgeIndex
      have totalBranchEquality := coverBranchEquiv_edgeIndex
        diagram root object cover projection covering
          ⟨sourceBranch, vertex, abuts⟩ edgeIndex
      have decodedVertexEquality : decoded.1.1 =
          (vertexComponentEquiv diagram root object cover projection covering
            vertex vertexComponent).1 := by
        have incidence := componentEquiv_incidence
          diagram root object cover projection covering
            ⟨sourceBranch, vertex, abuts⟩ edgeComponent
        rw [componentEquality] at incidence
        exact congrArg Subtype.val incidence.symm
      change cover.coincidence
          (edgeComponentEquiv
            diagram root object cover projection covering edge edgeComponent).1
          (coverBranchEquiv diagram root object cover projection edgeIndex
            sourceBranch) =
        some (vertexComponentEquiv diagram root object cover projection
          covering vertex vertexComponent).1
      change cover.coincidenceTotal
          (⟨edgeIndex.1, coverBranchEquiv
            diagram root object cover projection edgeIndex sourceBranch⟩ :
              cover.TotalBranch) = _
      rw [totalBranchEquality]
      exact (restrictedSourceIncidentBranch
        diagram root object cover projection covering
          ⟨sourceBranch, vertex, abuts⟩ decoded).2.trans
              (congrArg some decodedVertexEquality)

/-- The geometric comparison followed by the supplied graph projection agrees,
on vertices, with forgetting the repeated component index.  The target finite
component comparison makes the two presentations literal. -/
theorem finiteComponentComparison_coverComparison_projection_vertex
    [Countable cover.Vertex] [Countable cover.Edge]
    (vertex : CoverVertex diagram
      (covObject diagram root object cover projection covering)) :
    (finiteComponentComparison diagram root object).vertexMap
        (projection.vertexMap
          ((coverComparison diagram root object cover projection covering).vertexMap
            vertex)) =
      (coverSemiGraphMap diagram root
        (covObjectProjection diagram root object cover projection covering)).vertexMap
          vertex := by
  rcases vertex with ⟨vertex, component⟩
  induction component using Quotient.inductionOn' with
  | _ point =>
      have indexEquality :
          vertexComponentEquiv diagram root object cover projection covering
              vertex (Quotient.mk'' point) = point.1 :=
        SourceTemperoidComponentFamilyAction.componentEquiv_mk
          (diagram.vertexAnabelioid vertex).group
          ((diagram.vertexAnabelioid vertex).finiteAction
            (object.vertexObject vertex))
          (VertexIndex diagram root object cover projection vertex)
          (selectedVertexComponent
            diagram root object cover projection vertex) point
      simp only [coverComparison]
      rw [indexEquality]
      refine Sigma.ext point.1.2 ?_
      change HEq
        (finiteVertexComponentEquiv diagram root object
          (projection.vertexMap point.1.1).1
          (projection.vertexMap point.1.1).2)
        (Quotient.mk'' point.2.1)
      let rawComponent := finiteVertexComponentEquiv diagram root object
        (projection.vertexMap point.1.1).1
        (projection.vertexMap point.1.1).2
      have transportHEq : (point.1.2 ▸ rawComponent) ≍ rawComponent :=
        eqRec_heq_iff_heq.mpr HEq.rfl
      have selectedEquality := point.2.2.symm
      change (point.1.2 ▸ rawComponent) = Quotient.mk'' point.2.1
        at selectedEquality
      exact transportHEq.symm.trans (heq_of_eq selectedEquality)

/-- The geometric comparison followed by the supplied graph projection agrees,
on edges, with forgetting the repeated component index. -/
theorem finiteComponentComparison_coverComparison_projection_edge
    [Countable cover.Vertex] [Countable cover.Edge]
    (edge : CoverEdge diagram root
      (covObject diagram root object cover projection covering)) :
    (finiteComponentComparison diagram root object).edgeMap
        (projection.edgeMap
          ((coverComparison diagram root object cover projection covering).edgeMap
            edge)) =
      (coverSemiGraphMap diagram root
        (covObjectProjection diagram root object cover projection covering)).edgeMap
          edge := by
  rcases edge with ⟨edge, component⟩
  let reference :=
    SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      diagram root edge
  letI (targetEdge : diagram.base.Edge) :=
    (diagram.vertexAnabelioid
      (SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
        diagram root targetEdge).vertex).coverCategory
  letI (targetEdge : diagram.base.Edge) :=
    (diagram.edgeAnabelioid targetEdge).coverCategory
  induction component using Quotient.inductionOn' with
  | _ point =>
      let familyPoint :=
        (branchEdgeFamilyIso
          diagram root object cover projection covering reference).hom.hom.hom point
      have indexEquality :
          edgeComponentEquiv diagram root object cover projection covering edge
              (Quotient.mk'' point) = familyPoint.1 := by
        rfl
      simp only [coverComparison]
      rw [indexEquality]
      refine Sigma.ext familyPoint.1.2 ?_
      let edgeProjection := sourceTemperoidComponentFamilyProjection
        (diagram.edgeAnabelioid edge).group
        ((diagram.edgeAnabelioid edge).finiteAction
          (coverEdgeObject diagram root object edge))
        (EdgeIndex diagram root object cover projection edge)
        (selectedEdgeComponent diagram root object cover projection edge)
      have projectionCompatibility := ConcreteCategory.congr_hom
        (branchEdgeFamilyIso_projection
          diagram root object cover projection covering reference) point
      have underlyingEquality :
          (finiteEdgeIdentification diagram root object reference).inv.hom.hom
              familyPoint.2.1 =
            (reference.temperoidPullback.map
              ((covObjectProjection
                diagram root object cover projection covering).app
                  reference.vertex)).hom.hom point := by
        change familyPoint.2.1 =
            (finiteEdgeIdentification
              diagram root object reference).hom.hom.hom
              ((reference.temperoidPullback.map
                ((covObjectProjection
                  diagram root object cover projection covering).app
                    reference.vertex)).hom.hom point)
          at projectionCompatibility
        calc
          (finiteEdgeIdentification
              diagram root object reference).inv.hom.hom familyPoint.2.1 =
            (finiteEdgeIdentification
              diagram root object reference).inv.hom.hom
              ((finiteEdgeIdentification
                diagram root object reference).hom.hom.hom
                ((reference.temperoidPullback.map
                  ((covObjectProjection
                    diagram root object cover projection covering).app
                      reference.vertex)).hom.hom point)) :=
            congrArg _ projectionCompatibility
          _ = _ := ConcreteCategory.congr_hom
            (finiteEdgeIdentification
              diagram root object reference).hom_inv_id _
      change HEq
        (finiteEdgeComponentEquiv diagram root object
          (projection.edgeMap familyPoint.1.1).1
          (projection.edgeMap familyPoint.1.1).2)
        (Quotient.mk''
          ((reference.temperoidPullback.map
            ((covObjectProjection
              diagram root object cover projection covering).app
                reference.vertex)).hom.hom point))
      rw [← underlyingEquality]
      let rawComponent := finiteCanonicalEdgeComponentEquiv diagram root object
        (projection.edgeMap familyPoint.1.1).1
        (projection.edgeMap familyPoint.1.1).2
      have transportHEq : (familyPoint.1.2 ▸ rawComponent) ≍ rawComponent :=
        eqRec_heq_iff_heq.mpr HEq.rfl
      have selectedEquality := familyPoint.2.2.symm
      change (familyPoint.1.2 ▸ rawComponent) =
          Quotient.mk'' familyPoint.2.1 at selectedEquality
      have canonicalHEq : rawComponent ≍ Quotient.mk'' familyPoint.2.1 :=
        transportHEq.symm.trans (heq_of_eq selectedEquality)
      let toReference :
          (Σ targetEdge : diagram.base.Edge,
            SourceActionComponent (diagram.edgeAnabelioid targetEdge).group
              ((diagram.edgeAnabelioid targetEdge).finiteAction
                (coverEdgeObject diagram root object targetEdge))) →
            (Σ targetEdge : diagram.base.Edge,
              CoverEdgeComponent diagram root
                (finiteCovObject diagram root object) targetEdge) :=
        fun value => ⟨value.1,
          actionComponentEquiv
            (finiteEdgeIdentification diagram root object
              (SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
                diagram root value.1)).symm value.2⟩
      have canonicalSigmaEquality :
          (⟨(projection.edgeMap familyPoint.1.1).1, rawComponent⟩ :
            Σ targetEdge : diagram.base.Edge,
              SourceActionComponent (diagram.edgeAnabelioid targetEdge).group
                ((diagram.edgeAnabelioid targetEdge).finiteAction
                  (coverEdgeObject diagram root object targetEdge))) =
            ⟨edge, Quotient.mk'' familyPoint.2.1⟩ :=
        Sigma.ext familyPoint.1.2 canonicalHEq
      have referenceSigmaEquality := congrArg toReference canonicalSigmaEquality
      exact (Sigma.mk.inj_iff.mp referenceSigmaEquality).2

/-- Global vertex bijection underlying `coverComparison`. -/
noncomputable def coverVertexEquiv
    [Countable cover.Vertex] [Countable cover.Edge] :
    CoverVertex diagram
        (covObject diagram root object cover projection covering) ≃
      cover.Vertex :=
  (Equiv.sigmaCongrRight
    (vertexComponentEquiv
      diagram root object cover projection covering)).trans
      (Equiv.sigmaFiberEquiv
        (fun vertex : cover.Vertex ↦ (projection.vertexMap vertex).1))

/-- Global edge bijection underlying `coverComparison`. -/
noncomputable def coverEdgeEquiv
    [Countable cover.Vertex] [Countable cover.Edge] :
    CoverEdge diagram root
        (covObject diagram root object cover projection covering) ≃
      cover.Edge :=
  (Equiv.sigmaCongrRight
    (edgeComponentEquiv
      diagram root object cover projection covering)).trans
      (Equiv.sigmaFiberEquiv
        (fun liftedEdge : cover.Edge ↦ (projection.edgeMap liftedEdge).1))

theorem coverComparison_vertex_bijective
    [Countable cover.Vertex] [Countable cover.Edge] :
    Function.Bijective
      (coverComparison
        diagram root object cover projection covering).vertexMap :=
  (coverVertexEquiv
    diagram root object cover projection covering).bijective

theorem coverComparison_edge_bijective
    [Countable cover.Vertex] [Countable cover.Edge] :
    Function.Bijective
      (coverComparison
        diagram root object cover projection covering).edgeMap :=
  (coverEdgeEquiv
    diagram root object cover projection covering).bijective

/-- A nonverticial base branch remains nonverticial after lifting through the
supplied graph cover. -/
theorem coverBranch_coincidence_of_none
    {edge : diagram.base.Edge}
    (index : EdgeIndex diagram root object cover projection edge)
    (branch : diagram.base.Branch edge)
    (noVertex : diagram.base.coincidence edge branch = none) :
    cover.coincidence index.1
      (coverBranchEquiv diagram root object cover projection index branch) =
        none := by
  let liftedBranch := coverBranchEquiv
    diagram root object cover projection index branch
  have baseTotalEquality :
      (⟨(projection.edgeMap index.1).1,
          projection.branchEquiv index.1 liftedBranch⟩ :
        diagram.base.TotalBranch) = ⟨edge, branch⟩ :=
    Sigma.ext index.2 (coverBranchEquiv_projection_heq
      diagram root object cover projection index branch)
  have baseCoincidence :
      diagram.base.coincidence (projection.edgeMap index.1).1
          (projection.branchEquiv index.1 liftedBranch) = none :=
    (congrArg diagram.base.coincidenceTotal baseTotalEquality).trans noVertex
  have levelCoincidence :
      (LevelSemiGraph diagram root object).coincidence
          (projection.edgeMap index.1)
          (projection.branchEquiv index.1 liftedBranch) = none :=
    finiteEtaleCoverSemiGraph_coincidence_of_none
      diagram root object
        (component := (projection.edgeMap index.1).2) baseCoincidence
  cases sourceCoincidence : cover.coincidence index.1 liftedBranch with
  | none => rfl
  | some vertex =>
      have mappedCoincidence := projection.map_coincidence
        index.1 liftedBranch vertex sourceCoincidence
      rw [levelCoincidence] at mappedCoincidence
      cases mappedCoincidence

/-- The comparison neither creates nor removes verticial branches. -/
theorem coverComparison_isProper
    [Countable cover.Vertex] [Countable cover.Edge] :
    (coverComparison
      diagram root object cover projection covering).IsProper := by
  intro sourceEdge branch
  rcases sourceEdge with ⟨edge, component⟩
  cases baseCoincidence : diagram.base.coincidence edge branch with
  | some vertex =>
      let sourceVertex : CoverVertex diagram
          (covObject diagram root object cover projection covering) :=
        ⟨vertex, coverComponentMap diagram root
          (covObject diagram root object cover projection covering)
            ⟨branch, vertex, baseCoincidence⟩ component⟩
      have sourceCoincidence :
          (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph diagram root
            (covObject diagram root object cover projection covering)).coincidence
              ⟨edge, component⟩ branch = some sourceVertex :=
        SourceFiniteLevelUniversalCover.covCoverSemiGraph_coincidence_of_some
          diagram root
            (covObject diagram root object cover projection covering)
            component branch vertex baseCoincidence
      constructor
      · intro _
        exact ⟨(coverComparison diagram root object cover projection
            covering).vertexMap sourceVertex,
          (coverComparison diagram root object cover projection covering).map_coincidence
            ⟨edge, component⟩ branch sourceVertex
              sourceCoincidence⟩
      · intro _
        exact ⟨sourceVertex, sourceCoincidence⟩
  | none =>
      constructor
      · rintro ⟨sourceVertex, sourceCoincidence⟩
        rw [SourceFiniteLevelUniversalCover.covCoverSemiGraph_coincidence_of_none
          diagram root
            (covObject diagram root object cover projection covering)
            component branch baseCoincidence] at sourceCoincidence
        cases sourceCoincidence
      · rintro ⟨targetVertex, targetCoincidence⟩
        let index := edgeComponentEquiv
          diagram root object cover projection covering edge component
        change cover.coincidence index.1
            (coverBranchEquiv
              diagram root object cover projection index branch) =
          some targetVertex at targetCoincidence
        rw [coverBranch_coincidence_of_none
          diagram root object cover projection index branch baseCoincidence]
          at targetCoincidence
        cases targetCoincidence

/-- The comparison is locally bijective on incident branches. -/
theorem coverComparison_isExcision
    [Countable cover.Vertex] [Countable cover.Edge] :
    (coverComparison
      diagram root object cover projection covering).IsExcision := by
  let comparison := coverComparison
    diagram root object cover projection covering
  have vertexInjective :=
    (coverComparison_vertex_bijective
      diagram root object cover projection covering).1
  have edgeBijective := coverComparison_edge_bijective
    diagram root object cover projection covering
  have totalBranchInjective :
      Function.Injective comparison.totalBranchMap := by
    rintro ⟨firstEdge, firstBranch⟩ ⟨secondEdge, secondBranch⟩ equality
    have mappedEdgeEquality :
        comparison.edgeMap firstEdge = comparison.edgeMap secondEdge :=
      Sigma.mk.inj_iff.mp equality |>.1
    have edgeEquality : firstEdge = secondEdge :=
      edgeBijective.1 mappedEdgeEquality
    cases edgeEquality
    have branchEquality : firstBranch = secondBranch := by
      apply (comparison.branchEquiv firstEdge).injective
      exact eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
    exact Sigma.ext rfl (heq_of_eq branchEquality)
  intro sourceVertex
  constructor
  · intro first second equality
    apply Subtype.ext
    apply totalBranchInjective
    exact congrArg Subtype.val equality
  · rintro ⟨⟨targetEdge, targetBranch⟩, targetCoincidence⟩
    obtain ⟨sourceEdge, mappedEdgeEquality⟩ :=
      edgeBijective.2 targetEdge
    cases mappedEdgeEquality
    let sourceBranch := (comparison.branchEquiv sourceEdge).symm targetBranch
    have targetExists : ∃ targetVertex,
        cover.coincidence (comparison.edgeMap sourceEdge)
            (comparison.branchEquiv sourceEdge sourceBranch) =
          some targetVertex := by
      refine ⟨comparison.vertexMap sourceVertex, ?_⟩
      simpa only [sourceBranch, Equiv.apply_symm_apply] using targetCoincidence
    obtain ⟨actualSourceVertex, sourceCoincidence⟩ :=
      (coverComparison_isProper
        diagram root object cover projection covering
          sourceEdge sourceBranch).mpr targetExists
    have mappedCoincidence := comparison.map_coincidence
      sourceEdge sourceBranch actualSourceVertex sourceCoincidence
    have mappedVertexEquality :
        comparison.vertexMap actualSourceVertex =
          comparison.vertexMap sourceVertex := by
      apply Option.some.inj
      exact mappedCoincidence.symm.trans <| by
        simpa only [sourceBranch, Equiv.apply_symm_apply]
          using targetCoincidence
    have sourceVertexEquality : actualSourceVertex = sourceVertex :=
      vertexInjective mappedVertexEquality
    subst actualSourceVertex
    let sourceIncident :
        (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph diagram root
          (covObject diagram root object cover projection covering)).IncidentBranch
            sourceVertex :=
      ⟨⟨sourceEdge, sourceBranch⟩, sourceCoincidence⟩
    refine ⟨sourceIncident, ?_⟩
    apply Subtype.ext
    change (⟨comparison.edgeMap sourceEdge,
      comparison.branchEquiv sourceEdge sourceBranch⟩ : cover.TotalBranch) =
        ⟨comparison.edgeMap sourceEdge, targetBranch⟩
    exact Sigma.ext rfl <| heq_of_eq <|
      Equiv.apply_symm_apply (comparison.branchEquiv sourceEdge) targetBranch

/-- The realized component semigraph is a one-sheeted graph covering of the
supplied finite graph cover. -/
theorem coverComparison_isGraphCovering
    [Countable cover.Vertex] [Countable cover.Edge] :
    (coverComparison
      diagram root object cover projection covering).IsGraphCovering :=
  ⟨coverComparison_isProper
      diagram root object cover projection covering,
    coverComparison_isExcision
      diagram root object cover projection covering⟩

/-- If the supplied graph cover is finite, every constituent carrier of its
geometric realization is finite. -/
theorem covObject_isFiniteCover
    [Finite cover.Vertex] [Finite cover.Edge] :
    IsFiniteCover diagram
      (covObject diagram root object cover projection covering) := by
  intro vertex
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  change Finite (SourceTemperoidComponentFamilyCarrier
    (diagram.vertexAnabelioid vertex).group
    ((diagram.vertexAnabelioid vertex).finiteAction
      (object.vertexObject vertex))
    (VertexIndex diagram root object cover projection vertex)
    (selectedVertexComponent diagram root object cover projection vertex))
  infer_instance

/-- The actual finite object of `B(G)` recovered from a finite graph-cover
realization. -/
noncomputable def finiteObject
    [Finite cover.Vertex] [Finite cover.Edge] : diagram.GluedObject :=
  finiteRecoveryObject diagram
    (covObject diagram root object cover projection covering)
    (covObject_isFiniteCover
      diagram root object cover projection covering)

/-- The recovered finite object has the supplied graph cover as its literal
component semigraph, through the geometric realization comparison. -/
noncomputable def finiteObjectCovIso
    [Finite cover.Vertex] [Finite cover.Edge] :
    finiteCovObject diagram root
        (finiteObject diagram root object cover projection covering) ≅
      covObject diagram root object cover projection covering :=
  finiteRecoveryIso diagram root
    (covObject diagram root object cover projection covering)
    (covObject_isFiniteCover
      diagram root object cover projection covering)

/-- The finite object recovered from a finite graph cover has that graph cover
as its canonical finite-étale component semigraph. -/
noncomputable def finiteObjectCoverComparison
    [Finite cover.Vertex] [Finite cover.Edge] :
    (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
        diagram root
          (finiteObject diagram root object cover projection covering)).Hom
      cover :=
  ((finiteComponentComparison diagram root
      (finiteObject diagram root object cover projection covering)).comp
    (coverSemiGraphMap diagram root
      (finiteObjectCovIso
        diagram root object cover projection covering).hom)).comp
    (coverComparison diagram root object cover projection covering)

/-- The recovered finite object projects to the finite étale level from which
the graph cover was formed.  Full faithfulness of finite temperification lifts
the constituentwise copy-forgetting projection back to `B(G)`. -/
noncomputable def finiteObjectProjection
    [Finite cover.Vertex] [Finite cover.Edge] :
    finiteObject diagram root object cover projection covering ⟶ object :=
  (finiteInclusionFullyFaithful diagram root).preimage
    ((finiteObjectCovIso
        diagram root object cover projection covering).hom ≫
      covObjectProjection diagram root object cover projection covering)

/-- Temperifying `finiteObjectProjection` recovers the explicit geometric
projection: first identify the recovered object with the graph-cover
realization, then forget the graph-cover copy index. -/
theorem finiteInclusion_map_finiteObjectProjection
    [Finite cover.Vertex] [Finite cover.Edge] :
    (finiteInclusion diagram root).map
        (finiteObjectProjection
          diagram root object cover projection covering) =
      (finiteObjectCovIso
          diagram root object cover projection covering).hom ≫
        covObjectProjection diagram root object cover projection covering := by
  exact (finiteInclusionFullyFaithful diagram root).map_preimage _

/-- On vertices, the canonical recovered-cover comparison factors the supplied
graph-cover projection through the finite-étale transition induced by the
recovered object's projection. -/
theorem finiteObjectCoverComparison_vertex_factors
    [Finite cover.Vertex] [Finite cover.Edge]
    (vertex :
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
        diagram root
          (finiteObject diagram root object cover projection covering)).Vertex) :
    projection.vertexMap
        ((finiteObjectCoverComparison
          diagram root object cover projection covering).vertexMap vertex) =
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
        diagram root
          (finiteObjectProjection
            diagram root object cover projection covering)).vertexMap vertex := by
  apply finiteComponentComparison_vertex_injective diagram root object
  calc
    (finiteComponentComparison diagram root object).vertexMap
        (projection.vertexMap
          ((finiteObjectCoverComparison
            diagram root object cover projection covering).vertexMap vertex)) =
      (coverSemiGraphMap diagram root
        (covObjectProjection diagram root object cover projection covering)).vertexMap
          ((coverSemiGraphMap diagram root
            (finiteObjectCovIso
              diagram root object cover projection covering).hom).vertexMap
            ((finiteComponentComparison diagram root
              (finiteObject
                diagram root object cover projection covering)).vertexMap vertex)) :=
      finiteComponentComparison_coverComparison_projection_vertex
        diagram root object cover projection covering
          ((coverSemiGraphMap diagram root
            (finiteObjectCovIso
              diagram root object cover projection covering).hom).vertexMap
            ((finiteComponentComparison diagram root
              (finiteObject
                diagram root object cover projection covering)).vertexMap vertex))
    _ = (coverSemiGraphMap diagram root
          ((finiteObjectCovIso
              diagram root object cover projection covering).hom ≫
            covObjectProjection
              diagram root object cover projection covering)).vertexMap
          ((finiteComponentComparison diagram root
            (finiteObject
              diagram root object cover projection covering)).vertexMap vertex) :=
      (coverSemiGraphMap_vertex_comp diagram root
        (finiteObjectCovIso
          diagram root object cover projection covering).hom
        (covObjectProjection
          diagram root object cover projection covering)
        ((finiteComponentComparison diagram root
          (finiteObject
            diagram root object cover projection covering)).vertexMap vertex)).symm
    _ = (coverSemiGraphMap diagram root
          (finiteCovMap diagram root
            (finiteObjectProjection
              diagram root object cover projection covering))).vertexMap
          ((finiteComponentComparison diagram root
            (finiteObject
              diagram root object cover projection covering)).vertexMap vertex) := by
      have mapEquality :
          finiteCovMap diagram root
              (finiteObjectProjection
                diagram root object cover projection covering) =
            (finiteObjectCovIso
                diagram root object cover projection covering).hom ≫
              covObjectProjection
                diagram root object cover projection covering := by
        change (finiteInclusion diagram root).map
            (finiteObjectProjection
              diagram root object cover projection covering) = _
        exact finiteInclusion_map_finiteObjectProjection
          diagram root object cover projection covering
      exact congrArg
        (fun map => (coverSemiGraphMap diagram root map).vertexMap
          ((finiteComponentComparison diagram root
            (finiteObject
              diagram root object cover projection covering)).vertexMap vertex))
        mapEquality.symm
    _ = (finiteComponentComparison diagram root object).vertexMap
          ((SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
            diagram root
              (finiteObjectProjection
                diagram root object cover projection covering)).vertexMap vertex) :=
      (finiteComponentComparison_vertex_naturality
        diagram root
          (finiteObjectProjection
            diagram root object cover projection covering) vertex).symm

/-- On edges, the canonical recovered-cover comparison factors the supplied
graph-cover projection through the finite-étale transition induced by the
recovered object's projection. -/
theorem finiteObjectCoverComparison_edge_factors
    [Finite cover.Vertex] [Finite cover.Edge]
    (edge :
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
        diagram root
          (finiteObject diagram root object cover projection covering)).Edge) :
    projection.edgeMap
        ((finiteObjectCoverComparison
          diagram root object cover projection covering).edgeMap edge) =
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
        diagram root
          (finiteObjectProjection
            diagram root object cover projection covering)).edgeMap edge := by
  apply finiteComponentComparison_edge_injective diagram root object
  calc
    (finiteComponentComparison diagram root object).edgeMap
        (projection.edgeMap
          ((finiteObjectCoverComparison
            diagram root object cover projection covering).edgeMap edge)) =
      (coverSemiGraphMap diagram root
        (covObjectProjection diagram root object cover projection covering)).edgeMap
          ((coverSemiGraphMap diagram root
            (finiteObjectCovIso
              diagram root object cover projection covering).hom).edgeMap
            ((finiteComponentComparison diagram root
              (finiteObject
                diagram root object cover projection covering)).edgeMap edge)) :=
      finiteComponentComparison_coverComparison_projection_edge
        diagram root object cover projection covering
          ((coverSemiGraphMap diagram root
            (finiteObjectCovIso
              diagram root object cover projection covering).hom).edgeMap
            ((finiteComponentComparison diagram root
              (finiteObject
                diagram root object cover projection covering)).edgeMap edge))
    _ = (coverSemiGraphMap diagram root
          ((finiteObjectCovIso
              diagram root object cover projection covering).hom ≫
            covObjectProjection
              diagram root object cover projection covering)).edgeMap
          ((finiteComponentComparison diagram root
            (finiteObject
              diagram root object cover projection covering)).edgeMap edge) :=
      (coverSemiGraphMap_edge_comp diagram root
        (finiteObjectCovIso
          diagram root object cover projection covering).hom
        (covObjectProjection
          diagram root object cover projection covering)
        ((finiteComponentComparison diagram root
          (finiteObject
            diagram root object cover projection covering)).edgeMap edge)).symm
    _ = (coverSemiGraphMap diagram root
          (finiteCovMap diagram root
            (finiteObjectProjection
              diagram root object cover projection covering))).edgeMap
          ((finiteComponentComparison diagram root
            (finiteObject
              diagram root object cover projection covering)).edgeMap edge) := by
      have mapEquality :
          finiteCovMap diagram root
              (finiteObjectProjection
                diagram root object cover projection covering) =
            (finiteObjectCovIso
                diagram root object cover projection covering).hom ≫
              covObjectProjection
                diagram root object cover projection covering := by
        change (finiteInclusion diagram root).map
            (finiteObjectProjection
              diagram root object cover projection covering) = _
        exact finiteInclusion_map_finiteObjectProjection
          diagram root object cover projection covering
      exact congrArg
        (fun map => (coverSemiGraphMap diagram root map).edgeMap
          ((finiteComponentComparison diagram root
            (finiteObject
              diagram root object cover projection covering)).edgeMap edge))
        mapEquality.symm
    _ = (finiteComponentComparison diagram root object).edgeMap
          ((SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
            diagram root
              (finiteObjectProjection
                diagram root object cover projection covering)).edgeMap edge) :=
      (finiteComponentComparison_edge_naturality
        diagram root
          (finiteObjectProjection
            diagram root object cover projection covering) edge).symm

/-- The branch component of the recovered-cover comparison projects to the
same branch as the induced finite-étale transition. -/
theorem finiteObjectCoverComparison_branch_factors
    [Finite cover.Vertex] [Finite cover.Edge]
    (edge :
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
        diagram root
          (finiteObject diagram root object cover projection covering)).Edge)
    (branch :
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
        diagram root
          (finiteObject diagram root object cover projection covering)).Branch
            edge) :
    HEq
      (projection.branchEquiv
        ((finiteObjectCoverComparison
          diagram root object cover projection covering).edgeMap edge)
        ((finiteObjectCoverComparison
          diagram root object cover projection covering).branchEquiv edge branch))
      ((SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
        diagram root
          (finiteObjectProjection
            diagram root object cover projection covering)).branchEquiv
              edge branch) := by
  let geometricEdge := (coverSemiGraphMap diagram root
    (finiteObjectCovIso
      diagram root object cover projection covering).hom).edgeMap
    ((finiteComponentComparison diagram root
      (finiteObject
        diagram root object cover projection covering)).edgeMap edge)
  let index := edgeComponentEquiv
    diagram root object cover projection covering geometricEdge.1 geometricEdge.2
  change HEq
    (projection.branchEquiv index.1
      (coverBranchEquiv diagram root object cover projection index branch))
    branch
  exact coverBranchEquiv_projection_heq
    diagram root object cover projection index branch

/-- The canonical recovered-cover comparison followed by the supplied graph
projection is the finite-étale transition induced by the recovered projection. -/
theorem finiteObjectCoverComparison_factors
    [Finite cover.Vertex] [Finite cover.Edge] :
    (finiteObjectCoverComparison
        diagram root object cover projection covering).comp projection =
      SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
        diagram root
          (finiteObjectProjection
            diagram root object cover projection covering) := by
  apply SourceSemiGraph.Hom.ext
  · intro vertex
    exact finiteObjectCoverComparison_vertex_factors
      diagram root object cover projection covering vertex
  · intro edge
    exact finiteObjectCoverComparison_edge_factors
      diagram root object cover projection covering edge
  · intro edge branch
    exact
      finiteObjectCoverComparison_branch_factors
        diagram root object cover projection covering edge branch

/-- The canonical comparison with the recovered finite graph cover is proper.
This follows from its factorization through two already proper projections. -/
theorem finiteObjectCoverComparison_isProper
    [Finite cover.Vertex] [Finite cover.Edge] :
    (finiteObjectCoverComparison
      diagram root object cover projection covering).IsProper := by
  let comparison := finiteObjectCoverComparison
    diagram root object cover projection covering
  have compositeProper : (comparison.comp projection).IsProper := by
    rw [finiteObjectCoverComparison_factors]
    exact SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition_isProper
      diagram root
        (finiteObjectProjection
          diagram root object cover projection covering)
  intro edge branch
  exact (compositeProper edge branch).trans
    (covering.1 (comparison.edgeMap edge)
      (comparison.branchEquiv edge branch)).symm

/-- Choose a point in a finite-action orbit component. -/
noncomputable def pointOfComponent
    (G : ProfiniteGrp.{u}) (action : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G action) :
    SourceActionComponentFiber G action component := by
  let existence := Quotient.exists_rep component
  exact ⟨Classical.choose existence, Classical.choose_spec existence⟩

/-- A specified point in the component selected by a graph-cover root vertex
gives a point of the recovered finite object.  Keeping the representative
explicit is essential for point-preserving Galois refinement. -/
noncomputable def finiteObjectPoint
    [Finite cover.Vertex] [Finite cover.Edge]
    (rootVertex : VertexIndex diagram root object cover projection root)
    (point : SourceActionComponentFiber
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (object.vertexObject root))
      (selectedVertexComponent
        diagram root object cover projection root rootVertex)) :
    (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).obj
      (finiteObject diagram root object cover projection covering) := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  let geometricPoint :
      ((covObject diagram root object cover projection covering).vertexObject
        root).obj.V.obj :=
    ⟨rootVertex, point⟩
  exact (finiteRecoveryVertexIso diagram
    (covObject diagram root object cover projection covering)
    (covObject_isFiniteCover diagram root object cover projection covering)
      root).inv.hom.hom geometricPoint

/-- The recovered geometric projection sends an explicitly represented point
back to that same point of the original finite étale level. -/
theorem finiteObjectProjection_finiteObjectPoint
    [Finite cover.Vertex] [Finite cover.Edge]
    (rootVertex : VertexIndex diagram root object cover projection root)
    (point : SourceActionComponentFiber
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (object.vertexObject root))
      (selectedVertexComponent
        diagram root object cover projection root rootVertex)) :
    (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).map
        (finiteObjectProjection
          diagram root object cover projection covering)
        (finiteObjectPoint
          diagram root object cover projection covering rootVertex point) =
      point.1 := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  change (((finiteInclusion diagram root).map
      (finiteObjectProjection
        diagram root object cover projection covering)).app root).hom.hom
          (finiteObjectPoint
            diagram root object cover projection covering rootVertex point) =
        point.1
  rw [finiteInclusion_map_finiteObjectProjection]
  change ((covObjectProjection
      diagram root object cover projection covering).app root).hom.hom
        (((finiteObjectCovIso
          diagram root object cover projection covering).hom.app root).hom.hom
            (finiteObjectPoint
              diagram root object cover projection covering rootVertex point)) =
        point.1
  let geometricPoint :
      ((covObject diagram root object cover projection covering).vertexObject
        root).obj.V.obj := ⟨rootVertex, point⟩
  let recoveryIso := finiteRecoveryVertexIso diagram
    (covObject diagram root object cover projection covering)
    (covObject_isFiniteCover diagram root object cover projection covering) root
  have recoveryCancellation :
      recoveryIso.hom.hom.hom
          (recoveryIso.inv.hom.hom geometricPoint) = geometricPoint := by
    exact ConcreteCategory.congr_hom recoveryIso.inv_hom_id geometricPoint
  unfold finiteObjectPoint finiteObjectCovIso
  rw [finiteRecoveryIso_hom_app]
  change ((covObjectProjection
      diagram root object cover projection covering).app root).hom.hom
        (recoveryIso.hom.hom.hom
          (recoveryIso.inv.hom.hom geometricPoint)) = point.1
  rw [recoveryCancellation]
  rfl

/-- The finite-étale vertex represented by an explicit recovered point. -/
noncomputable def finiteObjectPointVertex
    [Finite cover.Vertex] [Finite cover.Edge]
    (rootVertex : VertexIndex diagram root object cover projection root)
    (point : SourceActionComponentFiber
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (object.vertexObject root))
      (selectedVertexComponent
        diagram root object cover projection root rootVertex)) :
    (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
      diagram root
        (finiteObject diagram root object cover projection covering)).Vertex :=
  ⟨root, Quotient.mk''
    (finiteObjectPoint
      diagram root object cover projection covering rootVertex point)⟩

/-- The recovered-cover comparison sends the vertex represented by the
chosen point to the graph-cover vertex from which that point was built. -/
theorem finiteObjectCoverComparison_finiteObjectPointVertex
    [Finite cover.Vertex] [Finite cover.Edge]
    (rootVertex : VertexIndex diagram root object cover projection root)
    (point : SourceActionComponentFiber
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (object.vertexObject root))
      (selectedVertexComponent
        diagram root object cover projection root rootVertex)) :
    (finiteObjectCoverComparison
      diagram root object cover projection covering).vertexMap
        (finiteObjectPointVertex
          diagram root object cover projection covering rootVertex point) =
      rootVertex.1 := by
  let geometricPoint :
      ((covObject diagram root object cover projection covering).vertexObject
        root).obj.V.obj :=
    ⟨rootVertex, point⟩
  let recoveryIso := finiteRecoveryVertexIso diagram
    (covObject diagram root object cover projection covering)
    (covObject_isFiniteCover diagram root object cover projection covering) root
  have recoveryCancellation :
      recoveryIso.hom.hom.hom
          (recoveryIso.inv.hom.hom geometricPoint) = geometricPoint :=
    ConcreteCategory.congr_hom recoveryIso.inv_hom_id geometricPoint
  have mappedVertex :
      (coverSemiGraphMap diagram root
        (finiteObjectCovIso
          diagram root object cover projection covering).hom).vertexMap
        ((finiteComponentComparison diagram root
          (finiteObject
            diagram root object cover projection covering)).vertexMap
          (finiteObjectPointVertex
            diagram root object cover projection covering rootVertex point)) =
      ⟨root, Quotient.mk'' geometricPoint⟩ := by
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply congrArg Quotient.mk''
    change recoveryIso.hom.hom.hom
        (recoveryIso.inv.hom.hom geometricPoint) = geometricPoint
    exact recoveryCancellation
  change (coverComparison
    diagram root object cover projection covering).vertexMap
      ((coverSemiGraphMap diagram root
        (finiteObjectCovIso
          diagram root object cover projection covering).hom).vertexMap
        ((finiteComponentComparison diagram root
          (finiteObject
            diagram root object cover projection covering)).vertexMap
          (finiteObjectPointVertex
            diagram root object cover projection covering rootVertex point))) =
      rootVertex.1
  rw [mappedVertex]
  have indexEquality :
      vertexComponentEquiv diagram root object cover projection covering
          root (Quotient.mk'' geometricPoint) = rootVertex :=
    SourceTemperoidComponentFamilyAction.componentEquiv_mk
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (object.vertexObject root))
      (VertexIndex diagram root object cover projection root)
      (selectedVertexComponent
        diagram root object cover projection root) geometricPoint
  change (vertexComponentEquiv
    diagram root object cover projection covering root
      (Quotient.mk'' geometricPoint)).1 = rootVertex.1
  rw [indexEquality]

/-- A graph-cover vertex above the distinguished base vertex supplies a point
of the recovered finite object. -/
noncomputable def finiteObjectRootPoint
    [Finite cover.Vertex] [Finite cover.Edge]
    (rootVertex : VertexIndex diagram root object cover projection root) :
    (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).obj
      (finiteObject diagram root object cover projection covering) := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  exact finiteObjectPoint diagram root object cover projection covering
    rootVertex (pointOfComponent
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (object.vertexObject root))
      (selectedVertexComponent
        diagram root object cover projection root rootVertex))

/-- An explicitly represented point of a finite graph-cover realization is
dominated by a Galois level, and the composite projection sends the selected
Galois point to the prescribed point of the original finite étale object. -/
theorem exists_galoisLevel_refinement_of_point
    [Finite cover.Vertex] [Finite cover.Edge]
    (rootVertex : VertexIndex diagram root object cover projection root)
    (point : SourceActionComponentFiber
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (object.vertexObject root))
      (selectedVertexComponent
        diagram root object cover projection root rootVertex)) :
    ∃ (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
        diagram root)
      (morphism : level.object ⟶
        finiteObject diagram root object cover projection covering),
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).map
          morphism level.point =
        finiteObjectPoint
          diagram root object cover projection covering rootVertex point ∧
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).map
          (morphism ≫ finiteObjectProjection
            diagram root object cover projection covering) level.point =
        point.1 := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : CategoryTheory.PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  obtain ⟨galoisObject, morphism, galoisPoint, isGalois, pointMaps⟩ :=
    CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root)
      (finiteObject diagram root object cover projection covering)
      (finiteObjectPoint
        diagram root object cover projection covering rootVertex point)
  refine ⟨⟨galoisObject, galoisPoint, isGalois⟩, morphism, pointMaps, ?_⟩
  rw [Functor.map_comp, FintypeCat.comp_apply, pointMaps,
    finiteObjectProjection_finiteObjectPoint]

/-- Every pointed finite graph-cover realization is dominated by an actual
pointed Galois level.  This is the categorical Galois-refinement step needed
after the finite graph quotient separates a deck transformation. -/
theorem exists_galoisLevel_refinement
    [Finite cover.Vertex] [Finite cover.Edge]
    (rootVertex : VertexIndex diagram root object cover projection root) :
    ∃ (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
        diagram root)
      (morphism : level.object ⟶
        finiteObject diagram root object cover projection covering),
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).map
          morphism level.point =
        finiteObjectRootPoint
          diagram root object cover projection covering rootVertex := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : CategoryTheory.PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  obtain ⟨galoisObject, morphism, galoisPoint, isGalois, pointMaps⟩ :=
    CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root)
      (finiteObject diagram root object cover projection covering)
      (finiteObjectRootPoint
        diagram root object cover projection covering rootVertex)
  exact ⟨⟨galoisObject, galoisPoint, isGalois⟩, morphism, pointMaps⟩

end SourceFiniteGraphCoverRealization

end Iut
