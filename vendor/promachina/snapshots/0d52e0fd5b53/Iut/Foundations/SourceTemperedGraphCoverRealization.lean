/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperoidRestrictionComponentFamily
import Iut.Foundations.SourceTemperedFiniteComponentComparison
import Iut.Foundations.SourceCombinatorialUniversalCover

/-!
# Realizing graph coverings of finite levels geometrically

A graph covering of the finite semi-graph attached to a finite étale cover
selects and repeats its constituent orbit components.  Restriction to an edge
refines each selected vertex orbit into edge-group orbits, while the local
bijectivity of the graph covering reindexes those edge orbits.  This file
turns that data into a literal object of `B^cov(G)`.
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

namespace SourcePointedAnabelioidHom

/-- The finite-action form of the pullback comparison. -/
noncomputable def finitePullbackActionIso
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourcePointedAnabelioidHom source target)
    (object : target.Cover) :
    letI := target.coverCategory
    letI := source.coverCategory
    sourceFiniteRestrictionAction morphism.fundamentalGroupHom
        (target.finiteAction object) ≅
      source.finiteAction (morphism.pullback.obj object) := by
  letI := target.coverCategory
  letI := source.coverCategory
  let comparison := morphism.finiteTemperificationPullbackIso.app object
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := FintypeCat.homMk (morphism.fiberIso.inv.app object)
        inv := FintypeCat.homMk (morphism.fiberIso.hom.app object)
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro point
          exact FintypeCat.inv_hom_id_apply
            (morphism.fiberIso.app object) point
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro point
          exact FintypeCat.hom_inv_id_apply
            (morphism.fiberIso.app object) point }
  · intro element
    apply ConcreteCategory.hom_ext
    intro point
    have equality := ConcreteCategory.congr_hom
      (comparison.inv.hom.comm element) point
    exact equality

end SourcePointedAnabelioidHom

namespace SourceSemiGraphOfAnabelioids.CovObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})

/-- Restrict the finite vertex action to an incident edge group and identify
it with the canonical reference-branch edge action. -/
noncomputable def finiteBranchActionIso
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (coverReferenceBranch diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    sourceFiniteRestrictionAction
        (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
        ((diagram.vertexAnabelioid branch.vertex).finiteAction
          (object.vertexObject branch.vertex)) ≅
      (diagram.edgeAnabelioid edge).finiteAction
        (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
          diagram root object edge) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact
    SourcePointedAnabelioidHom.finitePullbackActionIso
        (diagram.branchMorphism branch.branch branch.abuts)
        (object.vertexObject branch.vertex) ≪≫
      (EtaleFundamentalGroup.coverActionEquivalence
        (diagram.edgeAnabelioid edge)).functor.mapIso
        (object.glue branch reference)

/-- The finite and countable branch comparisons have the same forward point
map. -/
theorem finiteBranchActionIso_hom_apply
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (coverReferenceBranch diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ (point : (diagram.vertexAnabelioid branch.vertex).fiber.obj
      (object.vertexObject branch.vertex)),
    (finiteBranchActionIso diagram root object branch).hom.hom.hom point =
      (finiteEdgeIdentification diagram root object branch).hom.hom.hom point := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  intro point
  rfl

/-- The forward finite branch comparison is literally the countable branch
comparison after finite-action inclusion. -/
theorem finiteInclusion_map_finiteBranchActionIso_hom
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (coverReferenceBranch diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (SourceTemperoidAction.finiteInclusion
        (diagram.edgeAnabelioid edge).group).map
        (finiteBranchActionIso diagram root object branch).hom =
      (finiteEdgeIdentification diagram root object branch).hom := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  exact finiteBranchActionIso_hom_apply diagram root object branch point

/-- The finite and countable branch comparisons have the same inverse point
map. -/
theorem finiteBranchActionIso_inv_apply
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (coverReferenceBranch diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ (point : (diagram.edgeAnabelioid edge).fiber.obj
      (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
        diagram root object edge)),
    (finiteBranchActionIso diagram root object branch).inv.hom.hom point =
      (finiteEdgeIdentification diagram root object branch).inv.hom.hom point := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  intro point
  rfl

/-- The inverse finite branch comparison is literally the inverse countable
branch comparison after finite-action inclusion. -/
theorem finiteInclusion_map_finiteBranchActionIso_inv
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (coverReferenceBranch diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (SourceTemperoidAction.finiteInclusion
        (diagram.edgeAnabelioid edge).group).map
        (finiteBranchActionIso diagram root object branch).inv =
      (finiteEdgeIdentification diagram root object branch).inv := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  exact finiteBranchActionIso_inv_apply diagram root object branch point

/-- The fiber-functor edge components as components of the canonical finite
edge action. -/
noncomputable def finiteCanonicalEdgeComponentEquiv
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    (edge : diagram.base.Edge) :
    SourceSemiGraphOfAnabelioids.GluedObject.CoverEdgeComponent
        diagram root object edge ≃
      SourceActionComponent (diagram.edgeAnabelioid edge).group
        ((diagram.edgeAnabelioid edge).finiteAction
          (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
            diagram root object edge)) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact (diagram.edgeAnabelioid edge).fiberComponentFiniteActionEquiv
    (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
      diagram root object edge)

/-- The restricted edge component selected by the finite incidence map is
exactly the component transported through `finiteBranchActionIso`. -/
theorem finiteBranchComponentCompatibility
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (component :
      SourceSemiGraphOfAnabelioids.GluedObject.CoverEdgeComponent
        diagram root object edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (coverReferenceBranch diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    sourceFiniteRestrictionComponentMap
        (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
        ((diagram.vertexAnabelioid branch.vertex).finiteAction
          (object.vertexObject branch.vertex))
        ((sourceFiniteActionComponentEquiv
          (finiteBranchActionIso diagram root object branch)).symm
            (finiteCanonicalEdgeComponentEquiv
              diagram root object edge component)) =
      finiteVertexComponentEquiv diagram root object branch.vertex
        (SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
          diagram root object branch component) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  rw [finiteComponentEquiv_incidence]
  induction component using Quotient.inductionOn' with
  | _ point =>
      unfold finiteCanonicalEdgeComponentEquiv
      unfold finiteEdgeComponentEquiv
      unfold sourceFiniteRestrictionComponentMap
      unfold coverComponentMap
      simp only [ContAction.res_obj_obj, Action.res_obj_V, Equiv.trans_apply,
        Function.comp_apply]
      apply Quotient.sound
      change _ ∈ MulAction.orbit
        (diagram.vertexAnabelioid branch.vertex).group _
      rw [MulAction.mem_orbit_iff]
      refine ⟨1, ?_⟩
      rw [one_smul]
      rw [finiteBranchActionIso_inv_apply]
      have cancellation := congrArg
        (fun morphism ↦ morphism.hom.hom point)
        (finiteEdgeIdentification diagram root object reference).inv_hom_id
      exact congrArg
        (fun value ↦
          (finiteEdgeIdentification diagram root object branch).inv.hom.hom
            value)
        cancellation

end SourceSemiGraphOfAnabelioids.CovObject

namespace SourceFiniteLevelUniversalCover

open SourceCombinatorialUniversalCover
open SourceSemiGraphOfAnabelioids.GluedObject
open SourceSemiGraphOfAnabelioids.CovObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex) (object : diagram.GluedObject)

/-- The finite semigraph attached to the selected finite étale cover. -/
noncomputable abbrev LevelSemiGraph : SourceSemiGraph.{u} :=
  finiteEtaleCoverSemiGraph diagram root object

/-- Vertices of the combinatorial universal cover lying over a fixed base
vertex. -/
abbrev VertexIndex
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (vertex : diagram.base.Vertex) :=
  {lifted : SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedVertex
      (LevelSemiGraph diagram root object) levelRoot //
    lifted.vertex.1 = vertex}

/-- Edges of the combinatorial universal cover lying over a fixed base
edge. -/
abbrev EdgeIndex
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (edge : diagram.base.Edge) :=
  {lifted : SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
      (LevelSemiGraph diagram root object) levelRoot //
    lifted.edge.1 = edge}

noncomputable instance vertexIndex_countable
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (vertex : diagram.base.Vertex) :
    Countable (VertexIndex diagram root object levelRoot vertex) := by
  letI (baseVertex : diagram.base.Vertex) :=
    (diagram.vertexAnabelioid baseVertex).coverCategory
  letI : Countable
      (finiteEtaleCoverSemiGraph diagram root object).Vertex := by
    change Countable
      (SourceSemiGraphOfAnabelioids.GluedObject.CoverVertex diagram object)
    infer_instance
  letI (edge : diagram.base.Edge) :=
    (diagram.vertexAnabelioid
      (SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge).vertex).coverCategory
  letI (edge : diagram.base.Edge) :=
    (diagram.edgeAnabelioid edge).coverCategory
  letI : Countable
      (finiteEtaleCoverSemiGraph diagram root object).Edge := by
    change Countable
      (SourceSemiGraphOfAnabelioids.GluedObject.CoverEdge
        diagram root object)
    infer_instance
  letI : Countable
      (SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedVertex
        (finiteEtaleCoverSemiGraph diagram root object) levelRoot) :=
    inferInstance
  exact Function.Injective.countable Subtype.val_injective

noncomputable instance edgeIndex_countable
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (edge : diagram.base.Edge) :
    Countable (EdgeIndex diagram root object levelRoot edge) := by
  letI (baseVertex : diagram.base.Vertex) :=
    (diagram.vertexAnabelioid baseVertex).coverCategory
  letI : Countable
      (finiteEtaleCoverSemiGraph diagram root object).Vertex := by
    change Countable
      (SourceSemiGraphOfAnabelioids.GluedObject.CoverVertex diagram object)
    infer_instance
  letI (baseEdge : diagram.base.Edge) :=
    (diagram.vertexAnabelioid
      (SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root baseEdge).vertex).coverCategory
  letI (baseEdge : diagram.base.Edge) :=
    (diagram.edgeAnabelioid baseEdge).coverCategory
  letI : Countable
      (finiteEtaleCoverSemiGraph diagram root object).Edge := by
    change Countable
      (SourceSemiGraphOfAnabelioids.GluedObject.CoverEdge
        diagram root object)
    infer_instance
  letI : Countable
      (SourceCombinatorialUniversalCover.SourceSemiGraphUniversalCover.LiftedEdge
        (finiteEtaleCoverSemiGraph diagram root object) levelRoot) :=
    inferInstance
  exact Function.Injective.countable Subtype.val_injective

/-- The finite vertex-action component selected by a lifted universal-cover
vertex. -/
noncomputable def selectedVertexComponent
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (vertex : diagram.base.Vertex)
    (index : VertexIndex diagram root object levelRoot vertex) :
    SourceActionComponent (diagram.vertexAnabelioid vertex).group
      ((diagram.vertexAnabelioid vertex).finiteAction
        (object.vertexObject vertex)) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact index.2 ▸
    finiteVertexComponentEquiv diagram root object index.1.vertex.1
      index.1.vertex.2

/-- Componentwise comparison, retaining the base-vertex index. -/
noncomputable def totalFiniteVertexComponentEquiv :
    CoverVertex diagram object ≃
      Σ vertex : diagram.base.Vertex,
        SourceActionComponent (diagram.vertexAnabelioid vertex).group
          ((diagram.vertexAnabelioid vertex).finiteAction
            (object.vertexObject vertex)) := by
  letI (vertex : diagram.base.Vertex) :=
    (diagram.vertexAnabelioid vertex).coverCategory
  exact Equiv.sigmaCongrRight
    (fun vertex ↦ finiteVertexComponentEquiv diagram root object vertex)

/-- The vertex constituent obtained by repeating the finite orbit selected at
each lifted universal-cover vertex. -/
noncomputable def vertexAction
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (vertex : diagram.base.Vertex) :
    SourceTemperoidAction (diagram.vertexAnabelioid vertex).group := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact sourceTemperoidComponentFamilyAction
    (diagram.vertexAnabelioid vertex).group
    ((diagram.vertexAnabelioid vertex).finiteAction
      (object.vertexObject vertex))
    (VertexIndex diagram root object levelRoot vertex)
    (selectedVertexComponent diagram root object levelRoot vertex)

/-- Components obtained by restricting the selected vertex families along an
incident edge branch. -/
abbrev RestrictedBranchIndex
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :=
  SourceRestrictedComponentFamilyIndex
    (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom
    ((diagram.vertexAnabelioid branch.vertex).finiteAction
      (object.vertexObject branch.vertex))
    (VertexIndex diagram root object levelRoot branch.vertex)
    (selectedVertexComponent diagram root object levelRoot branch.vertex)

/-- The finite edge component encoded by one restricted component of a
selected vertex orbit. -/
noncomputable def restrictedFiniteEdgeComponent
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object levelRoot branch) :
    CoverEdgeComponent diagram root object edge := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact
    (finiteCanonicalEdgeComponentEquiv diagram root object edge).symm
      (sourceFiniteActionComponentEquiv
        (finiteBranchActionIso diagram root object branch) index.2.1)

/-- The edge component encoded by a restricted orbit is incident to the
finite component carried by its selected lifted vertex. -/
theorem restrictedFiniteEdgeComponent_incidence
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object levelRoot branch) :
    finiteVertexComponentEquiv diagram root object branch.vertex
        (coverComponentMap diagram root object branch
          (restrictedFiniteEdgeComponent
            diagram root object levelRoot branch index)) =
      selectedVertexComponent diagram root object levelRoot branch.vertex
        index.1 := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  rw [← finiteBranchComponentCompatibility
    diagram root object branch
      (restrictedFiniteEdgeComponent diagram root object levelRoot branch
        index)]
  unfold restrictedFiniteEdgeComponent
  rw [Equiv.apply_symm_apply]
  rw [Equiv.symm_apply_apply]
  exact index.2.2

/-- The finite-level incidence selected by a restricted component lands at
the finite vertex carried by its lifted index. -/
theorem restrictedFiniteEdgeComponent_incidentVertex
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object levelRoot branch) :
    (⟨branch.vertex,
      coverComponentMap diagram root object branch
        (restrictedFiniteEdgeComponent
          diagram root object levelRoot branch index)⟩ :
        (LevelSemiGraph diagram root object).Vertex) =
      index.1.1.vertex := by
  apply (totalFiniteVertexComponentEquiv diagram root object).injective
  apply Sigma.ext index.1.2.symm
  exact (heq_of_eq (restrictedFiniteEdgeComponent_incidence
      diagram root object levelRoot branch index)).trans
    (eqRec_heq index.1.2
      ((finiteVertexComponentEquiv diagram root object index.1.1.vertex.1)
        index.1.1.vertex.2))

/-- The incident branch in the finite level encoded by a restricted vertex
component. -/
noncomputable def restrictedFiniteIncidentBranch
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object levelRoot branch) :
    (LevelSemiGraph diagram root object).IncidentBranch index.1.1.vertex := by
  let component := restrictedFiniteEdgeComponent
    diagram root object levelRoot branch index
  refine ⟨⟨⟨edge, component⟩, branch.branch⟩, ?_⟩
  change (finiteEtaleCoverSemiGraph diagram root object).coincidence
    ⟨edge, component⟩ branch.branch = some index.1.1.vertex
  rw [finiteEtaleCoverSemiGraph_coincidence_of_some
    diagram root object branch.abuts]
  exact congrArg some
    (restrictedFiniteEdgeComponent_incidentVertex
      diagram root object levelRoot branch index)

/-- Lift a restricted component's finite-level incidence to the unique edge
of the combinatorial universal cover. -/
noncomputable def restrictedBranchIndexToEdgeIndex
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    RestrictedBranchIndex diagram root object levelRoot branch →
      EdgeIndex diagram root object levelRoot edge :=
  fun index ↦
    ⟨SourceSemiGraphUniversalCover.incidentEdge
      (LevelSemiGraph diagram root object) levelRoot index.1.1
      (restrictedFiniteIncidentBranch
        diagram root object levelRoot branch index), rfl⟩

/-- Recover the restricted vertex component incident to a lifted universal
edge. -/
noncomputable def liftedEdgeToRestrictedBranchIndex
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (liftedEdge : SourceSemiGraphUniversalCover.LiftedEdge
      (LevelSemiGraph diagram root object) levelRoot)
    (branch : diagram.IncidentBranch liftedEdge.edge.1) :
    RestrictedBranchIndex diagram root object levelRoot branch := by
  let component := liftedEdge.edge.2
  have sourceCoincidence :
      (LevelSemiGraph diagram root object).coincidence
          liftedEdge.edge branch.branch =
        some ⟨branch.vertex,
          coverComponentMap diagram root object branch component⟩ :=
    finiteEtaleCoverSemiGraph_coincidence_of_some
      diagram root object branch.abuts
  let liftedVertex : SourceSemiGraphUniversalCover.LiftedVertex
      (LevelSemiGraph diagram root object) levelRoot :=
    ⟨SourceSemiGraphUniversalCover.compactVertexPath
        (LevelSemiGraph diagram root object) levelRoot liftedEdge branch.branch,
      ⟨branch.vertex,
        coverComponentMap diagram root object branch component⟩, by
        rw [SourceSemiGraphUniversalCover.compactVertexPath_endpoint,
          SourceSemiGraphUniversalCover.compactEndpoint_of_some
            (LevelSemiGraph diagram root object) sourceCoincidence]⟩
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root liftedEdge.edge.1
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid liftedEdge.edge.1).coverCategory
  let restrictedComponent :=
    (sourceFiniteActionComponentEquiv
      (finiteBranchActionIso diagram root object branch)).symm
        (finiteCanonicalEdgeComponentEquiv
          diagram root object liftedEdge.edge.1 component)
  refine ⟨⟨liftedVertex, rfl⟩, ⟨restrictedComponent, ?_⟩⟩
  simpa only [restrictedComponent, selectedVertexComponent, liftedVertex]
    using finiteBranchComponentCompatibility
      diagram root object branch component

/-- Recover the restricted vertex component incident to a lifted universal
edge whose base edge is specified propositionally. -/
noncomputable def edgeIndexToRestrictedBranchIndex
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    EdgeIndex diagram root object levelRoot edge →
      RestrictedBranchIndex diagram root object levelRoot branch
  | ⟨liftedEdge, edgeEquality⟩ => by
      cases edgeEquality
      exact liftedEdgeToRestrictedBranchIndex
        diagram root object levelRoot liftedEdge branch

@[simp]
theorem edgeIndexToRestrictedBranchIndex_refl
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (liftedEdge : SourceSemiGraphUniversalCover.LiftedEdge
      (LevelSemiGraph diagram root object) levelRoot)
    (branch : diagram.IncidentBranch liftedEdge.edge.1) :
    edgeIndexToRestrictedBranchIndex diagram root object levelRoot branch
        ⟨liftedEdge, rfl⟩ =
      liftedEdgeToRestrictedBranchIndex
        diagram root object levelRoot liftedEdge branch := by
  rfl

/-- Decoding and re-encoding a lifted edge preserves its finite edge
component. -/
theorem restrictedFiniteEdgeComponent_edgeIndexToRestricted
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : EdgeIndex diagram root object levelRoot edge) :
    restrictedFiniteEdgeComponent diagram root object levelRoot branch
        (edgeIndexToRestrictedBranchIndex
          diagram root object levelRoot branch index) =
      index.2 ▸ index.1.edge.2 := by
  rcases index with ⟨liftedEdge, edgeEquality⟩
  change liftedEdge.edge.1 = edge at edgeEquality
  cases edgeEquality
  rw [edgeIndexToRestrictedBranchIndex_refl]
  unfold liftedEdgeToRestrictedBranchIndex
  unfold restrictedFiniteEdgeComponent
  rw [Equiv.apply_symm_apply]
  rw [Equiv.symm_apply_apply]

theorem restrictedBranchIndexToEdgeIndex_rightInverse
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    Function.RightInverse
      (edgeIndexToRestrictedBranchIndex
        diagram root object levelRoot branch)
      (restrictedBranchIndexToEdgeIndex
        diagram root object levelRoot branch) := by
  rintro ⟨liftedEdge, edgeEquality⟩
  change liftedEdge.edge.1 = edge at edgeEquality
  cases edgeEquality
  apply Subtype.ext
  apply SourceSemiGraphUniversalCover.LiftedEdge.path_injective
  unfold restrictedBranchIndexToEdgeIndex
  rw [edgeIndexToRestrictedBranchIndex_refl]
  let decoded := liftedEdgeToRestrictedBranchIndex
    diagram root object levelRoot liftedEdge branch
  let decodedVertex := decoded.1.1
  have sourceCoincidence :
      (LevelSemiGraph diagram root object).coincidence
          liftedEdge.edge branch.branch =
        some ⟨branch.vertex,
          coverComponentMap diagram root object branch liftedEdge.edge.2⟩ :=
    finiteEtaleCoverSemiGraph_coincidence_of_some
      diagram root object branch.abuts
  have decodedVertex_eq : decodedVertex =
      { path := SourceSemiGraphUniversalCover.compactVertexPath
          (LevelSemiGraph diagram root object) levelRoot liftedEdge
            branch.branch
        vertex := ⟨branch.vertex,
          coverComponentMap diagram root object branch liftedEdge.edge.2⟩
        endpoint_eq := by
          rw [SourceSemiGraphUniversalCover.compactVertexPath_endpoint,
            SourceSemiGraphUniversalCover.compactEndpoint_of_some
              (LevelSemiGraph diagram root object) sourceCoincidence] } := by
    rfl
  have liftedCoincidence :
      SourceSemiGraphUniversalCover.coincidence
          (LevelSemiGraph diagram root object) levelRoot
            liftedEdge branch.branch =
        some decodedVertex := by
    rw [decodedVertex_eq]
    exact SourceSemiGraphUniversalCover.coincidence_eq_some_of_eq_some
      (LevelSemiGraph diagram root object) levelRoot liftedEdge
        branch.branch _ sourceCoincidence
  let liftedBranch :
      (SourceSemiGraphUniversalCover.semiGraphCover
        (LevelSemiGraph diagram root object) levelRoot).IncidentBranch
          decodedVertex :=
    ⟨⟨liftedEdge, branch.branch⟩, liftedCoincidence⟩
  have incidentEquality :
      restrictedFiniteIncidentBranch diagram root object levelRoot branch
          decoded =
        (SourceSemiGraphUniversalCover.projection
          (LevelSemiGraph diagram root object) levelRoot).incidentBranchMap
            decodedVertex liftedBranch := by
    apply Subtype.ext
    change (⟨⟨liftedEdge.edge.1,
          restrictedFiniteEdgeComponent diagram root object levelRoot branch
            decoded⟩, branch.branch⟩ :
        (LevelSemiGraph diagram root object).TotalBranch) =
      ⟨liftedEdge.edge, branch.branch⟩
    apply Sigma.ext
    · change (⟨liftedEdge.edge.1,
          restrictedFiniteEdgeComponent diagram root object levelRoot branch
            decoded⟩ :
          SourceSemiGraphOfAnabelioids.GluedObject.CoverEdge
            diagram root object) = liftedEdge.edge
      exact Sigma.ext rfl <| heq_of_eq
        (restrictedFiniteEdgeComponent_edgeIndexToRestricted
          diagram root object levelRoot branch ⟨liftedEdge, rfl⟩)
    · rfl
  change (SourceSemiGraphUniversalCover.incidentEdge
      (LevelSemiGraph diagram root object) levelRoot decodedVertex
        (restrictedFiniteIncidentBranch
          diagram root object levelRoot branch decoded)).path = liftedEdge.path
  rw [incidentEquality]
  exact congrArg SourceSemiGraphUniversalCover.LiftedEdge.path
    (SourceSemiGraphUniversalCover.incidentEdge_projection
      (LevelSemiGraph diagram root object) levelRoot decodedVertex liftedBranch)

/-- A restricted branch index is determined by its lifted vertex and its
restricted finite-action component; the remaining fields are proofs. -/
theorem restrictedBranchIndex_encoding_injective
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    Function.Injective (fun index :
      RestrictedBranchIndex diagram root object levelRoot branch ↦
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

theorem restrictedBranchIndexToEdgeIndex_leftInverse
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    Function.LeftInverse
      (edgeIndexToRestrictedBranchIndex
        diagram root object levelRoot branch)
      (restrictedBranchIndexToEdgeIndex
        diagram root object levelRoot branch) := by
  intro index
  unfold restrictedBranchIndexToEdgeIndex
  let liftedEdge := SourceSemiGraphUniversalCover.incidentEdge
    (LevelSemiGraph diagram root object) levelRoot index.1.1
      (restrictedFiniteIncidentBranch
        diagram root object levelRoot branch index)
  change edgeIndexToRestrictedBranchIndex
      diagram root object levelRoot branch ⟨liftedEdge, rfl⟩ = index
  change liftedEdgeToRestrictedBranchIndex
      diagram root object levelRoot liftedEdge branch = index
  apply restrictedBranchIndex_encoding_injective
    diagram root object levelRoot branch
  apply Prod.ext
  · apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    dsimp only [liftedEdge]
    exact SourceSemiGraphUniversalCover.compactVertexPath_incidentEdge
      (LevelSemiGraph diagram root object) levelRoot index.1.1
        (restrictedFiniteIncidentBranch
          diagram root object levelRoot branch index)
  · unfold liftedEdgeToRestrictedBranchIndex
    dsimp only [liftedEdge]
    change (sourceFiniteActionComponentEquiv
        (finiteBranchActionIso diagram root object branch)).symm
          (finiteCanonicalEdgeComponentEquiv diagram root object edge
            (restrictedFiniteEdgeComponent
              diagram root object levelRoot branch index)) = index.2.1
    unfold restrictedFiniteEdgeComponent
    rw [Equiv.apply_symm_apply]
    rw [Equiv.symm_apply_apply]

/-- Local incidence reindexes the restricted component family at either
branch by the common family of lifted universal-cover edges. -/
noncomputable def restrictedBranchIndexEquivEdgeIndex
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    RestrictedBranchIndex diagram root object levelRoot branch ≃
      EdgeIndex diagram root object levelRoot edge where
  toFun := restrictedBranchIndexToEdgeIndex
    diagram root object levelRoot branch
  invFun := edgeIndexToRestrictedBranchIndex
    diagram root object levelRoot branch
  left_inv := restrictedBranchIndexToEdgeIndex_leftInverse
    diagram root object levelRoot branch
  right_inv := restrictedBranchIndexToEdgeIndex_rightInverse
    diagram root object levelRoot branch

/-- The finite canonical edge-action component selected by a lifted universal
edge. -/
noncomputable def selectedEdgeComponent
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (edge : diagram.base.Edge)
    (index : EdgeIndex diagram root object levelRoot edge) :
    SourceActionComponent (diagram.edgeAnabelioid edge).group
      ((diagram.edgeAnabelioid edge).finiteAction
        (coverEdgeObject diagram root object edge)) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact index.2 ▸
    finiteCanonicalEdgeComponentEquiv
      diagram root object index.1.edge.1 index.1.edge.2

/-- The branch comparison sends each restricted vertex component to the
finite edge component carried by the corresponding lifted edge. -/
theorem branchComponentCompatibility
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (index : RestrictedBranchIndex diagram root object levelRoot branch) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
        diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    sourceFiniteActionComponentEquiv
        (finiteBranchActionIso diagram root object branch) index.2.1 =
      selectedEdgeComponent diagram root object levelRoot edge
        (restrictedBranchIndexEquivEdgeIndex
          diagram root object levelRoot branch index) := by
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  unfold restrictedBranchIndexEquivEdgeIndex
  unfold restrictedBranchIndexToEdgeIndex
  unfold selectedEdgeComponent
  change sourceFiniteActionComponentEquiv
      (finiteBranchActionIso diagram root object branch) index.2.1 =
    finiteCanonicalEdgeComponentEquiv diagram root object edge
      (restrictedFiniteEdgeComponent
        diagram root object levelRoot branch index)
  unfold restrictedFiniteEdgeComponent
  rw [Equiv.apply_symm_apply]

/-- The common edge constituent indexed by lifted universal-cover edges. -/
noncomputable def edgeAction
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
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
    (EdgeIndex diagram root object levelRoot edge)
    (selectedEdgeComponent diagram root object levelRoot edge)

/-- Restriction of a vertex family along an incident branch is canonically
the common lifted-edge family. -/
noncomputable def branchEdgeFamilyIso
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    branch.temperoidPullback.obj
        (vertexAction diagram root object levelRoot branch.vertex) ≅
      edgeAction diagram root object levelRoot edge := by
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
        (VertexIndex diagram root object levelRoot branch.vertex)
        (selectedVertexComponent
          diagram root object levelRoot branch.vertex) ≪≫
      sourceTemperoidComponentFamilyActionIso
        (finiteBranchActionIso diagram root object branch)
        (fun index : RestrictedBranchIndex
          diagram root object levelRoot branch ↦ index.2.1)
        (selectedEdgeComponent diagram root object levelRoot edge)
        (restrictedBranchIndexEquivEdgeIndex
          diagram root object levelRoot branch)
        (branchComponentCompatibility
          diagram root object levelRoot branch)

/-- The geometric countable cover whose component semigraph is the
combinatorial universal cover of the chosen finite étale level. -/
noncomputable def covObject
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    diagram.CovObject where
  vertexObject := vertexAction diagram root object levelRoot
  glue := fun first second ↦
    branchEdgeFamilyIso diagram root object levelRoot first ≪≫
      (branchEdgeFamilyIso diagram root object levelRoot second).symm
  glue_refl := by
    intro edge branch
    simp
  glue_trans := by
    intro edge first second third
    simp

/-- Orbit components of the geometric vertex constituent are exactly the
lifted universal-cover vertices over that base vertex. -/
noncomputable def vertexComponentEquiv
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (vertex : diagram.base.Vertex) :
    SourceSemiGraphOfAnabelioids.CovObject.CoverVertexComponent diagram
        (covObject diagram root object levelRoot) vertex ≃
      VertexIndex diagram root object levelRoot vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact SourceTemperoidComponentFamilyAction.componentEquiv
    (diagram.vertexAnabelioid vertex).group
    ((diagram.vertexAnabelioid vertex).finiteAction
      (object.vertexObject vertex))
    (VertexIndex diagram root object levelRoot vertex)
    (selectedVertexComponent diagram root object levelRoot vertex)

/-- Orbit components of the representative geometric edge constituent are
exactly the lifted universal-cover edges over that base edge. -/
noncomputable def edgeComponentEquiv
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    (edge : diagram.base.Edge) :
    SourceSemiGraphOfAnabelioids.CovObject.CoverEdgeComponent diagram root
        (covObject diagram root object levelRoot) edge ≃
      EdgeIndex diagram root object levelRoot edge := by
  let reference :=
    SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
      diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact (actionComponentEquiv
    (branchEdgeFamilyIso diagram root object levelRoot reference)).trans
      (SourceTemperoidComponentFamilyAction.componentEquiv
        (diagram.edgeAnabelioid edge).group
        ((diagram.edgeAnabelioid edge).finiteAction
          (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
            diagram root object edge))
        (EdgeIndex diagram root object levelRoot edge)
        (selectedEdgeComponent diagram root object levelRoot edge))

/-- The concrete carrier equivalence underlying an isomorphism of temperoid
actions. -/
noncomputable def actionCarrierEquiv
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second : SourceTemperoidAction G}
    (identification : first ≅ second) :
    first.obj.V.obj ≃ second.obj.V.obj where
  toFun := identification.hom.hom.hom
  invFun := identification.inv.hom.hom
  left_inv point := by
    exact congrArg
      (fun morphism : first ⟶ first ↦ morphism.hom.hom point)
      identification.hom_inv_id
  right_inv point := by
    exact congrArg
      (fun morphism : second ⟶ second ↦ morphism.hom.hom point)
      identification.inv_hom_id

theorem actionCarrierEquiv_smul
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second : SourceTemperoidAction G}
    (identification : first ≅ second) (g : G)
    (point : first.obj.V.obj) :
    actionCarrierEquiv identification (g • point) =
      g • actionCarrierEquiv identification point := by
  exact ConcreteCategory.congr_hom
    (identification.hom.hom.comm g) point

/-- The kernel-splitting condition is invariant under isomorphism of both
the splitter and the target action. -/
theorem actionKernelFixes_transport
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {splitter splitter' target target' : SourceTemperoidAction G}
    (splitterIdentification : splitter ≅ splitter')
    (targetIdentification : target ≅ target')
    (fixes : SourceSemiGraphOfAnabelioids.CovObject.ActionKernelFixes
      splitter target) :
    SourceSemiGraphOfAnabelioids.CovObject.ActionKernelFixes
      splitter' target' := by
  intro g fixesSplitter' point
  let splitterEquiv := actionCarrierEquiv splitterIdentification
  let targetEquiv := actionCarrierEquiv targetIdentification
  have fixesSplitter : ∀ sourcePoint : splitter.obj.V.obj,
      g • sourcePoint = sourcePoint := by
    intro sourcePoint
    apply splitterEquiv.injective
    rw [actionCarrierEquiv_smul]
    exact fixesSplitter' (splitterEquiv sourcePoint)
  apply targetEquiv.symm.injective
  change actionCarrierEquiv targetIdentification.symm (g • point) =
    actionCarrierEquiv targetIdentification.symm point
  rw [actionCarrierEquiv_smul]
  exact fixes g fixesSplitter (targetEquiv.symm point)

/-- The kernel of a finite action fixes every repeated family of its orbit
components. -/
theorem finiteActionKernelFixesComponentFamily
    (G : ProfiniteGrp.{u}) (action : ContAction FintypeCat.{u} G)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent G action) :
    SourceSemiGraphOfAnabelioids.CovObject.ActionKernelFixes
      ((SourceTemperoidAction.finiteInclusion G).obj action)
      (sourceTemperoidComponentFamilyAction G action Index component) := by
  intro g fixes point
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact fixes point.2.1

/-- The finite level itself splits the geometric universal-cover object. -/
theorem covObject_isSplitBy
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    SourceSemiGraphOfAnabelioids.CovObject.IsSplitBy diagram root object
      (covObject diagram root object levelRoot) := by
  constructor
  · intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact finiteActionKernelFixesComponentFamily
      (diagram.vertexAnabelioid vertex).group
      ((diagram.vertexAnabelioid vertex).finiteAction
        (object.vertexObject vertex))
      (VertexIndex diagram root object levelRoot vertex)
      (selectedVertexComponent diagram root object levelRoot vertex)
  · intro edge
    let reference :=
      SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    let canonicalFixes := finiteActionKernelFixesComponentFamily
      (diagram.edgeAnabelioid edge).group
      ((diagram.edgeAnabelioid edge).finiteAction
        (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
          diagram root object edge))
      (EdgeIndex diagram root object levelRoot edge)
      (selectedEdgeComponent diagram root object levelRoot edge)
    exact actionKernelFixes_transport
      (SourceSemiGraphOfAnabelioids.CovObject.finiteEdgeIdentification
        diagram root object reference).symm
      (branchEdgeFamilyIso
        diagram root object levelRoot reference).symm
      canonicalFixes

/-- Hence the geometric universal-cover object is tempered, with its finite
level retained as the explicit splitter witness. -/
theorem covObject_isTempered
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    SourceSemiGraphOfAnabelioids.CovObject.IsTempered diagram root
      (covObject diagram root object levelRoot) :=
  SourceSemiGraphOfAnabelioids.CovObject.isTempered_of_isSplitBy diagram root
    (covObject_isSplitBy diagram root object levelRoot)

/-- The component incidence of the geometric object is the local incidence
of the combinatorial universal cover, expressed through the branch index
equivalence. -/
theorem componentEquiv_incidence
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (component :
      SourceSemiGraphOfAnabelioids.CovObject.CoverEdgeComponent diagram root
        (covObject diagram root object levelRoot) edge) :
    vertexComponentEquiv diagram root object levelRoot branch.vertex
        (SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
          diagram root (covObject diagram root object levelRoot)
            branch component) =
      ((restrictedBranchIndexEquivEdgeIndex
        diagram root object levelRoot branch).symm
          (edgeComponentEquiv
            diagram root object levelRoot edge component)).1 := by
  induction component using Quotient.inductionOn' with
  | _ point =>
      rfl

/-- Transport a base branch to the branch fiber of a lifted universal-cover
edge. -/
noncomputable def liftedEdgeBranchEquiv
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge}
    (index : EdgeIndex diagram root object levelRoot edge) :
    diagram.base.Branch edge ≃
      (SourceSemiGraphUniversalCover.semiGraphCover
        (LevelSemiGraph diagram root object) levelRoot).Branch index.1 :=
  Equiv.cast (congrArg diagram.base.Branch index.2.symm)

/-- Evaluation of universal-cover coincidence in terms of the decoded local
restricted component. -/
theorem liftedEdge_coincidence
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge}
    (index : EdgeIndex diagram root object levelRoot edge)
    (branch : diagram.base.Branch edge) (vertex : diagram.base.Vertex)
    (abuts : diagram.base.coincidence edge branch = some vertex) :
    SourceSemiGraphUniversalCover.coincidence
        (LevelSemiGraph diagram root object) levelRoot index.1
          (liftedEdgeBranchEquiv
            diagram root object levelRoot index branch) =
      some ((edgeIndexToRestrictedBranchIndex
        diagram root object levelRoot ⟨branch, vertex, abuts⟩ index).1.1) := by
  rcases index with ⟨liftedEdge, edgeEquality⟩
  change liftedEdge.edge.1 = edge at edgeEquality
  cases edgeEquality
  rw [edgeIndexToRestrictedBranchIndex_refl]
  exact SourceSemiGraphUniversalCover.coincidence_eq_some_of_eq_some
    (LevelSemiGraph diagram root object) levelRoot liftedEdge branch
      ⟨vertex, coverComponentMap diagram root object
        ⟨branch, vertex, abuts⟩ liftedEdge.edge.2⟩
      (finiteEtaleCoverSemiGraph_coincidence_of_some
        diagram root object abuts)

/-- The associated component semigraph maps canonically to the combinatorial
universal cover of the finite level. -/
noncomputable def coverComparison
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph diagram root
      (covObject diagram root object levelRoot)).Hom
        (SourceSemiGraphUniversalCover.semiGraphCover
          (LevelSemiGraph diagram root object) levelRoot) where
  vertexMap := fun point ↦
    (vertexComponentEquiv diagram root object levelRoot point.1 point.2).1
  edgeMap := fun point ↦
    (edgeComponentEquiv diagram root object levelRoot point.1 point.2).1
  branchEquiv := fun point ↦ liftedEdgeBranchEquiv
    diagram root object levelRoot
      (edgeComponentEquiv diagram root object levelRoot point.1 point.2)
  map_coincidence := by
    intro sourceEdge branch sourceVertex coincidence
    rcases sourceEdge with ⟨edge, edgeComponent⟩
    rcases sourceVertex with ⟨vertex, vertexComponent⟩
    change (match abuts : diagram.base.coincidence edge branch with
      | none => none
      | some target => some (⟨target,
          SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
            diagram root (covObject diagram root object levelRoot)
              ⟨branch, target, abuts⟩ edgeComponent⟩ :
            SourceSemiGraphOfAnabelioids.CovObject.CoverVertex diagram
              (covObject diagram root object levelRoot))) =
        some (⟨vertex, vertexComponent⟩ :
          SourceSemiGraphOfAnabelioids.CovObject.CoverVertex diagram
            (covObject diagram root object levelRoot)) at coincidence
    split at coincidence
    next noVertex => cases coincidence
    next target abuts =>
      have vertexEquality : target = vertex :=
        Sigma.mk.inj_iff.mp (Option.some.inj coincidence) |>.1
      subst target
      have componentEquality :
          SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
              diagram root (covObject diagram root object levelRoot)
                ⟨branch, vertex, abuts⟩ edgeComponent = vertexComponent :=
        eq_of_heq (Sigma.mk.inj_iff.mp
          (Option.some.inj coincidence) |>.2)
      change SourceSemiGraphUniversalCover.coincidence
          (LevelSemiGraph diagram root object) levelRoot
            (edgeComponentEquiv
              diagram root object levelRoot edge edgeComponent).1
            (liftedEdgeBranchEquiv diagram root object levelRoot
              (edgeComponentEquiv
                diagram root object levelRoot edge edgeComponent) branch) =
        some (vertexComponentEquiv
          diagram root object levelRoot vertex vertexComponent).1
      rw [liftedEdge_coincidence diagram root object levelRoot
        (edgeComponentEquiv
          diagram root object levelRoot edge edgeComponent)
        branch vertex abuts]
      apply congrArg some
      have indexEquality := componentEquiv_incidence
        diagram root object levelRoot ⟨branch, vertex, abuts⟩ edgeComponent
      rw [componentEquality] at indexEquality
      exact congrArg Subtype.val indexEquality.symm

/-- Global vertex bijection underlying `coverComparison`. -/
noncomputable def coverVertexEquiv
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    SourceSemiGraphOfAnabelioids.CovObject.CoverVertex diagram
        (covObject diagram root object levelRoot) ≃
      SourceSemiGraphUniversalCover.LiftedVertex
        (LevelSemiGraph diagram root object) levelRoot :=
  (Equiv.sigmaCongrRight
    (vertexComponentEquiv diagram root object levelRoot)).trans
      (Equiv.sigmaFiberEquiv
        (fun lifted : SourceSemiGraphUniversalCover.LiftedVertex
          (LevelSemiGraph diagram root object) levelRoot ↦ lifted.vertex.1))

/-- Global edge bijection underlying `coverComparison`. -/
noncomputable def coverEdgeEquiv
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    SourceSemiGraphOfAnabelioids.CovObject.CoverEdge diagram root
        (covObject diagram root object levelRoot) ≃
      SourceSemiGraphUniversalCover.LiftedEdge
        (LevelSemiGraph diagram root object) levelRoot :=
  (Equiv.sigmaCongrRight
    (edgeComponentEquiv diagram root object levelRoot)).trans
      (Equiv.sigmaFiberEquiv
        (fun lifted : SourceSemiGraphUniversalCover.LiftedEdge
          (LevelSemiGraph diagram root object) levelRoot ↦ lifted.edge.1))

theorem coverComparison_vertex_bijective
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    Function.Bijective
      (coverComparison diagram root object levelRoot).vertexMap :=
  (coverVertexEquiv diagram root object levelRoot).bijective

theorem coverComparison_edge_bijective
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    Function.Bijective
      (coverComparison diagram root object levelRoot).edgeMap :=
  (coverEdgeEquiv diagram root object levelRoot).bijective

@[simp]
theorem covCoverSemiGraph_coincidence_of_some
    (target : diagram.CovObject) {edge : diagram.base.Edge}
    (component : SourceSemiGraphOfAnabelioids.CovObject.CoverEdgeComponent
      diagram root target edge)
    (branch : diagram.base.Branch edge) (vertex : diagram.base.Vertex)
    (abuts : diagram.base.coincidence edge branch = some vertex) :
    (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
      diagram root target).coincidence ⟨edge, component⟩ branch =
      some ⟨vertex,
        SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
          diagram root target ⟨branch, vertex, abuts⟩ component⟩ := by
  change (match actual : diagram.base.coincidence edge branch with
    | none => none
    | some targetVertex => some (⟨targetVertex,
        SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
          diagram root target ⟨branch, targetVertex, actual⟩ component⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.CoverVertex
          diagram target)) = _
  split
  next noVertex =>
    rw [abuts] at noVertex
    contradiction
  next actualVertex actual =>
    have vertexEquality : actualVertex = vertex :=
      Option.some.inj (actual.symm.trans abuts)
    subst actualVertex
    rfl

@[simp]
theorem covCoverSemiGraph_coincidence_of_none
    (target : diagram.CovObject) {edge : diagram.base.Edge}
    (component : SourceSemiGraphOfAnabelioids.CovObject.CoverEdgeComponent
      diagram root target edge)
    (branch : diagram.base.Branch edge)
    (noVertex : diagram.base.coincidence edge branch = none) :
    (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
      diagram root target).coincidence ⟨edge, component⟩ branch = none := by
  change (match actual : diagram.base.coincidence edge branch with
    | none => none
    | some targetVertex => some (⟨targetVertex,
        SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
          diagram root target ⟨branch, targetVertex, actual⟩ component⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.CoverVertex
          diagram target)) = none
  split
  next _ => rfl
  next vertex actual =>
    rw [noVertex] at actual
    contradiction

theorem liftedEdge_coincidence_of_none
    (levelRoot : (LevelSemiGraph diagram root object).Vertex)
    {edge : diagram.base.Edge}
    (index : EdgeIndex diagram root object levelRoot edge)
    (branch : diagram.base.Branch edge)
    (noVertex : diagram.base.coincidence edge branch = none) :
    SourceSemiGraphUniversalCover.coincidence
        (LevelSemiGraph diagram root object) levelRoot index.1
          (liftedEdgeBranchEquiv
            diagram root object levelRoot index branch) = none := by
  rcases index with ⟨liftedEdge, edgeEquality⟩
  change liftedEdge.edge.1 = edge at edgeEquality
  cases edgeEquality
  change SourceSemiGraphUniversalCover.coincidence
    (LevelSemiGraph diagram root object) levelRoot liftedEdge branch = none
  have finiteCoincidence :
      (LevelSemiGraph diagram root object).coincidence
        liftedEdge.edge branch = none := by
    simpa only [Sigma.eta] using
      (finiteEtaleCoverSemiGraph_coincidence_of_none
        diagram root object (component := liftedEdge.edge.2) noVertex)
  unfold SourceSemiGraphUniversalCover.coincidence
  split
  next _ => rfl
  next vertex actual =>
    rw [finiteCoincidence] at actual
    contradiction

/-- The comparison neither creates nor removes verticial branches. -/
theorem coverComparison_isProper
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    (coverComparison diagram root object levelRoot).IsProper := by
  intro sourceEdge branch
  rcases sourceEdge with ⟨edge, component⟩
  cases baseCoincidence : diagram.base.coincidence edge branch with
  | some vertex =>
      let sourceVertex :
          SourceSemiGraphOfAnabelioids.CovObject.CoverVertex diagram
            (covObject diagram root object levelRoot) :=
        ⟨vertex,
          SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
            diagram root (covObject diagram root object levelRoot)
              ⟨branch, vertex, baseCoincidence⟩ component⟩
      have sourceCoincidence :
          (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
            diagram root (covObject diagram root object levelRoot)).coincidence
              ⟨edge, component⟩ branch = some sourceVertex := by
        exact covCoverSemiGraph_coincidence_of_some diagram root
          (covObject diagram root object levelRoot) component branch vertex
            baseCoincidence
      constructor
      · intro _
        exact ⟨(coverComparison diagram root object levelRoot).vertexMap
            sourceVertex,
          (coverComparison diagram root object levelRoot).map_coincidence
            ⟨edge, component⟩ branch sourceVertex sourceCoincidence⟩
      · intro _
        exact ⟨sourceVertex, sourceCoincidence⟩
  | none =>
      constructor
      · rintro ⟨sourceVertex, sourceCoincidence⟩
        rw [covCoverSemiGraph_coincidence_of_none diagram root
          (covObject diagram root object levelRoot) component branch
            baseCoincidence] at sourceCoincidence
        cases sourceCoincidence
      · rintro ⟨targetVertex, targetCoincidence⟩
        let index := edgeComponentEquiv
          diagram root object levelRoot edge component
        change SourceSemiGraphUniversalCover.coincidence
            (LevelSemiGraph diagram root object) levelRoot index.1
              (liftedEdgeBranchEquiv
                diagram root object levelRoot index branch) =
          some targetVertex at targetCoincidence
        rw [liftedEdge_coincidence_of_none diagram root object levelRoot
          index branch baseCoincidence] at targetCoincidence
        cases targetCoincidence

/-- The comparison is locally bijective on incident branches. -/
theorem coverComparison_isExcision
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    (coverComparison diagram root object levelRoot).IsExcision := by
  let comparison := coverComparison diagram root object levelRoot
  have vertexInjective :=
    (coverComparison_vertex_bijective
      diagram root object levelRoot).1
  have edgeBijective := coverComparison_edge_bijective
    diagram root object levelRoot
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
        (SourceSemiGraphUniversalCover.semiGraphCover
          (LevelSemiGraph diagram root object) levelRoot).coincidence
            (comparison.edgeMap sourceEdge)
            (comparison.branchEquiv sourceEdge sourceBranch) =
          some targetVertex := by
      refine ⟨comparison.vertexMap sourceVertex, ?_⟩
      simpa only [sourceBranch, Equiv.apply_symm_apply] using targetCoincidence
    obtain ⟨actualSourceVertex, sourceCoincidence⟩ :=
      (coverComparison_isProper diagram root object levelRoot
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
          (covObject diagram root object levelRoot)).IncidentBranch
            sourceVertex :=
      ⟨⟨sourceEdge, sourceBranch⟩, sourceCoincidence⟩
    refine ⟨sourceIncident, ?_⟩
    apply Subtype.ext
    change (⟨comparison.edgeMap sourceEdge,
      comparison.branchEquiv sourceEdge sourceBranch⟩ :
        (SourceSemiGraphUniversalCover.semiGraphCover
          (LevelSemiGraph diagram root object) levelRoot).TotalBranch) =
      ⟨comparison.edgeMap sourceEdge, targetBranch⟩
    exact Sigma.ext rfl <| heq_of_eq <|
      Equiv.apply_symm_apply (comparison.branchEquiv sourceEdge) targetBranch

/-- The component semigraph is a one-sheeted graph covering of the
combinatorial universal cover. -/
theorem coverComparison_isGraphCovering
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    (coverComparison diagram root object levelRoot).IsGraphCovering :=
  ⟨coverComparison_isProper diagram root object levelRoot,
    coverComparison_isExcision diagram root object levelRoot⟩

/-- The geometric component semi-graph of the finite-level universal cover
is connected.  The one-sheeted comparison reflects connectedness from the
combinatorial universal cover. -/
theorem coverSemiGraph_isConnected
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (levelRoot : (LevelSemiGraph diagram root object).Vertex) :
    (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph diagram root
      (covObject diagram root object levelRoot)).IsConnected :=
  source_isConnected_of_bijective_hom
    (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph diagram root
      (covObject diagram root object levelRoot))
    (SourceSemiGraphUniversalCover.semiGraphCover
      (LevelSemiGraph diagram root object) levelRoot)
    (coverComparison diagram root object levelRoot)
    (coverComparison_isProper diagram root object levelRoot)
    (coverComparison_vertex_bijective diagram root object levelRoot)
    (coverComparison_edge_bijective diagram root object levelRoot)
    (SourceSemiGraphUniversalCover.semiGraphCover_isConnected
      (LevelSemiGraph diagram root object) levelRoot)

end SourceFiniteLevelUniversalCover

end Iut
