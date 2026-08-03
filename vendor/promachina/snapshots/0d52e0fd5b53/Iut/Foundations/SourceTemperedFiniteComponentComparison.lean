/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperoidComponentFamily
import Iut.Foundations.SourceGluedFiniteEtaleCover
import Iut.Foundations.SourceConnectedFiniteEtaleConverse
import Iut.Foundations.SourceTemperedCoveringCategory

/-!
# Finite-cover components in the geometric and action presentations

The finite semi-graph attached to an object of an anabelioid is indexed by
orbits under automorphisms of the fiber functor.  Its temperification is
indexed by orbits under the certified profinite fundamental group.  The
fundamental-group certificate identifies these two actions, so their orbit
sets are canonically equivalent.
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

namespace EtaleFundamentalGroup

/-- The finite continuous action associated to a finite cover. -/
noncomputable abbrev finiteAction
    (data : EtaleFundamentalGroup.{u}) (object : data.Cover) :
    ContAction FintypeCat.{u} data.group := by
  letI := data.coverCategory
  exact (coverActionEquivalence data).functor.obj object

/-- The fiber-functor component set and the certified-group component set of
a finite cover are the same orbits, transported across the certified
fundamental-group equivalence. -/
noncomputable def fiberComponentFiniteActionEquiv
    (data : EtaleFundamentalGroup.{u}) (object : data.Cover) :
    data.FiberComponent object ≃
      SourceActionComponent data.group (data.finiteAction object) := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  letI (X : data.Cover) : MulAction data.group (data.fiber.obj X) :=
    data.action X
  let comparison :=
    SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv data
  let forward : data.FiberComponent object →
      SourceActionComponent data.group (data.finiteAction object) :=
    Quotient.map' id (by
      intro first second relation
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
      obtain ⟨automorphism, equality⟩ := relation
      refine ⟨comparison.symm automorphism, ?_⟩
      change comparison.symm automorphism • second = first
      rw [← SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_hom_app]
      change (comparison (comparison.symm automorphism)).hom.app object second =
        first
      rw [comparison.apply_symm_apply]
      exact equality)
  let reverse : SourceActionComponent data.group (data.finiteAction object) →
      data.FiberComponent object :=
    Quotient.map' id (by
      intro first second relation
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
      obtain ⟨element, equality⟩ := relation
      refine ⟨comparison element, ?_⟩
      change (comparison element).hom.app object second = first
      rw [SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_hom_app]
      exact equality)
  exact
    { toFun := forward
      invFun := reverse
      left_inv := by
        intro component
        induction component using Quotient.inductionOn' with
        | _ point => rfl
      right_inv := by
        intro component
        induction component using Quotient.inductionOn' with
        | _ point => rfl }

/-- Temperification does not change the point map of a finite-cover
morphism. -/
theorem finiteTemperification_map_apply
    (data : EtaleFundamentalGroup.{u}) :
    letI := data.coverCategory
    ∀ {first second : data.Cover} (map : first ⟶ second)
      (point : data.fiber.obj first),
      (data.finiteTemperification.map map).hom.hom point =
        data.fiber.map map point := by
  letI := data.coverCategory
  intro first second map point
  rfl

/-- Passing from fiber-functor components to components of the associated
finite action is natural in a finite-cover morphism. -/
theorem fiberComponentFiniteActionEquiv_naturality
    (data : EtaleFundamentalGroup.{u}) :
    letI := data.coverCategory
    ∀ {source target : data.Cover} (map : source ⟶ target)
      (component : data.FiberComponent source),
      fiberComponentFiniteActionEquiv data target
          (fiberComponentHomMap data map component) =
        SourceSemiGraphOfAnabelioids.CovObject.actionComponentMap
          (data.finiteTemperification.map map)
          (fiberComponentFiniteActionEquiv data source component) := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  intro source target map component
  induction component using Quotient.inductionOn' with
  | _ point => rfl

end EtaleFundamentalGroup

namespace SourcePointedAnabelioidHom

/-- The finite-temperification pullback comparison acts on points by the
chosen fiber-functor comparison. -/
theorem finiteTemperificationPullbackIso_hom_apply
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourcePointedAnabelioidHom source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    ∀ (object : target.Cover)
      (point : source.fiber.obj (morphism.pullback.obj object)),
      ((morphism.finiteTemperificationPullbackIso.app object).hom.hom.hom point) =
        morphism.fiberIso.hom.app object point := by
  letI := target.coverCategory
  letI := source.coverCategory
  intro object point
  rfl

end SourcePointedAnabelioidHom

namespace SourceSemiGraphOfAnabelioids.CovObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})

/-- Reversing a gluing comparison is the comparison in the opposite
direction. -/
theorem glue_inv_eq_reverse_hom
    (object : diagram.CovObject)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    (object.glue first second).inv = (object.glue second first).hom := by
  apply (cancel_epi (object.glue first second).hom).1
  rw [Iso.hom_inv_id]
  have coherence := congrArg Iso.hom
    (object.glue_trans first second first)
  rw [object.glue_refl] at coherence
  simpa only [Iso.trans_hom, Iso.refl_hom] using coherence.symm

/-- Vertex components in the finite-etale semigraph agree with the vertex
components of the same finite cover viewed in `B^cov(G)`. -/
noncomputable def finiteVertexComponentEquiv
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    (vertex : diagram.base.Vertex) :
    SourceSemiGraphOfAnabelioids.GluedObject.CoverVertexComponent
        diagram object vertex ≃
      CoverVertexComponent diagram
        (finiteCovObject diagram root object) vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact (diagram.vertexAnabelioid vertex).fiberComponentFiniteActionEquiv
    (object.vertexObject vertex)

/-- Edge components in the finite-etale semigraph agree with the edge
components of the same finite cover viewed in `B^cov(G)`.  The comparison
uses the same reference-branch identification as `finiteCovObject`. -/
noncomputable def finiteEdgeComponentEquiv
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    (edge : diagram.base.Edge) :
    SourceSemiGraphOfAnabelioids.GluedObject.CoverEdgeComponent
        diagram root object edge ≃
      CoverEdgeComponent diagram root
        (finiteCovObject diagram root object) edge := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact
    ((diagram.edgeAnabelioid edge).fiberComponentFiniteActionEquiv
      (SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeObject
        diagram root object edge)).trans
      (actionComponentEquiv
        (finiteEdgeIdentification diagram root object reference)).symm

/-- The vertex and edge component comparisons preserve the incidence map of
the finite cover. -/
theorem finiteComponentEquiv_incidence
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (component :
      SourceSemiGraphOfAnabelioids.GluedObject.CoverEdgeComponent
        diagram root object edge) :
    finiteVertexComponentEquiv diagram root object branch.vertex
        (SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
          diagram root object branch component) =
      coverComponentMap diagram root
        (finiteCovObject diagram root object) branch
        (finiteEdgeComponentEquiv diagram root object edge component) := by
  unfold finiteVertexComponentEquiv finiteEdgeComponentEquiv
  induction component using Quotient.inductionOn' with
  | _ point =>
      apply Quotient.sound
      change _ ∈ MulAction.orbit
        (diagram.vertexAnabelioid branch.vertex).group _
      rw [MulAction.mem_orbit_iff]
      refine ⟨1, ?_⟩
      rw [one_smul]
      let reference := coverReferenceBranch diagram root edge
      letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
      letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
      letI := (diagram.edgeAnabelioid edge).coverCategory
      rw [finiteCovObject_glue_hom]
      simp only [finiteEdgeIdentification,
        SourceSemiGraphOfAnabelioids.GluedObject.coverEdgeIdentification,
        object.glue_refl,
        ContAction.res_obj_obj, Action.res_obj_V, Functor.comp_obj,
        Iso.app_inv, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
        Action.comp_hom, id_eq]
      have fiberIdentity :
          (diagram.edgeAnabelioid edge).fiber.map
              (𝟙 (reference.pullback.obj
                (object.vertexObject reference.vertex))) point = point := by
        have equality := congrArg
          (fun morphism ↦ morphism point)
          ((diagram.edgeAnabelioid edge).fiber.map_id
            (reference.pullback.obj
              (object.vertexObject reference.vertex)))
        exact equality
      dsimp only [reference] at fiberIdentity
      let referenceComparison :=
        (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
          (diagram.branchMorphism reference.branch reference.abuts)).app
            (object.vertexObject reference.vertex)
      let branchComparison :=
        (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
          (diagram.branchMorphism branch.branch branch.abuts)).app
            (object.vertexObject branch.vertex)
      let edgeMap :=
        (diagram.edgeAnabelioid edge).finiteTemperification.map
          (object.glue reference branch).hom
      let transportedMap :=
        referenceComparison.inv ≫ edgeMap ≫ branchComparison.hom
      have cancellation :
          referenceComparison.hom ≫ transportedMap =
            edgeMap ≫ branchComparison.hom := by
        dsimp only [transportedMap]
        simp
        rfl
      calc
        _ = (referenceComparison.hom ≫ transportedMap).hom.hom
              ((diagram.edgeAnabelioid edge).fiber.map
                (𝟙 (reference.pullback.obj
                  (object.vertexObject reference.vertex))) point) := rfl
        _ = (referenceComparison.hom ≫ transportedMap).hom.hom point :=
          congrArg _ fiberIdentity
        _ = (edgeMap ≫ branchComparison.hom).hom.hom point :=
          congrArg (fun morphism ↦ morphism.hom.hom point) cancellation
        _ = _ := by
          change
            branchComparison.hom.hom
                (edgeMap.hom.hom point) =
              (diagram.branchMorphism branch.branch branch.abuts).fiberIso.hom.app
                (object.vertexObject branch.vertex)
                  ((diagram.edgeAnabelioid edge).fiber.map
                    (object.glue reference branch).hom point)
          rw [EtaleFundamentalGroup.finiteTemperification_map_apply]
          exact SourcePointedAnabelioidHom.finiteTemperificationPullbackIso_hom_apply
            (diagram.branchMorphism branch.branch branch.abuts)
            (object.vertexObject branch.vertex)
            ((diagram.edgeAnabelioid edge).fiber.map
              (object.glue reference branch).hom point)

/-- The comparison of finite vertex components with tempered orbit components
is natural in the finite glued object. -/
theorem finiteVertexComponentEquiv_naturality
    (root : diagram.base.Vertex)
    {source target : diagram.GluedObject} (map : source ⟶ target)
    (vertex : diagram.base.Vertex)
    (component :
      SourceSemiGraphOfAnabelioids.GluedObject.CoverVertexComponent
        diagram source vertex) :
    finiteVertexComponentEquiv diagram root target vertex
        (EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.vertexAnabelioid vertex) (map.app vertex) component) =
      coverVertexComponentMap diagram (finiteCovMap diagram root map) vertex
        (finiteVertexComponentEquiv diagram root source vertex component) := by
  unfold finiteVertexComponentEquiv coverVertexComponentMap finiteCovMap
  exact EtaleFundamentalGroup.fiberComponentFiniteActionEquiv_naturality
    (diagram.vertexAnabelioid vertex) (map.app vertex) component

/-- The comparison of finite edge components with tempered orbit components is
natural in the finite glued object. -/
theorem finiteEdgeComponentEquiv_naturality
    (root : diagram.base.Vertex)
    {source target : diagram.GluedObject} (map : source ⟶ target)
    (edge : diagram.base.Edge)
    (component :
      SourceSemiGraphOfAnabelioids.GluedObject.CoverEdgeComponent
        diagram root source edge) :
    finiteEdgeComponentEquiv diagram root target edge
        (EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.edgeAnabelioid edge)
          (let reference := coverReferenceBranch diagram root edge
           letI :=
             (diagram.vertexAnabelioid reference.vertex).coverCategory
           letI := (diagram.edgeAnabelioid edge).coverCategory
           reference.pullback.map (map.app reference.vertex)) component) =
      coverEdgeComponentMap diagram root (finiteCovMap diagram root map) edge
        (finiteEdgeComponentEquiv diagram root source edge component) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  induction component using Quotient.inductionOn' with
  | _ point =>
      apply congrArg Quotient.mk''
      simpa only [EtaleFundamentalGroup.finiteTemperification_map_apply,
        id_eq] using
          (ConcreteCategory.congr_hom
            (finiteEdgeIdentification_inv_naturality
              diagram root map reference) point).symm

/-- The finite-etale semigraph of an object is canonically its component
semigraph after finite temperification. -/
noncomputable def finiteComponentComparison
    (root : diagram.base.Vertex) (object : diagram.GluedObject) :
    (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
      diagram root object).Hom
      (coverSemiGraph diagram root (finiteCovObject diagram root object)) where
  vertexMap := fun vertex =>
    ⟨vertex.1, finiteVertexComponentEquiv diagram root object vertex.1 vertex.2⟩
  edgeMap := fun edge =>
    ⟨edge.1, finiteEdgeComponentEquiv diagram root object edge.1 edge.2⟩
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    rintro ⟨edge, component⟩ branch ⟨vertex, vertexComponent⟩ coincidence
    change (match sourceAbuts : diagram.base.coincidence edge branch with
      | none => none
      | some targetVertex => some (⟨targetVertex,
          SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
            diagram root object
              ⟨branch, targetVertex, sourceAbuts⟩ component⟩ :
                SourceSemiGraphOfAnabelioids.GluedObject.CoverVertex
                  diagram object)) =
        some (⟨vertex, vertexComponent⟩ :
          SourceSemiGraphOfAnabelioids.GluedObject.CoverVertex diagram object)
      at coincidence
    split at coincidence
    next noVertex => cases coincidence
    next targetVertex sourceAbuts =>
      have vertexEquality : targetVertex = vertex :=
        Sigma.mk.inj_iff.mp (Option.some.inj coincidence) |>.1
      subst targetVertex
      have componentEquality :
          SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap
              diagram root object ⟨branch, vertex, sourceAbuts⟩ component =
            vertexComponent :=
        eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj coincidence) |>.2)
      change (match targetAbuts : diagram.base.coincidence edge branch with
        | none => none
        | some targetVertex => some (⟨targetVertex,
            coverComponentMap diagram root (finiteCovObject diagram root object)
              ⟨branch, targetVertex, targetAbuts⟩
              (finiteEdgeComponentEquiv diagram root object edge component)⟩ :
                CoverVertex diagram (finiteCovObject diagram root object))) = _
      split
      next targetNone =>
        rw [sourceAbuts] at targetNone
        cases targetNone
      next targetVertex targetAbuts =>
        have targetVertexEquality : targetVertex = vertex :=
          Option.some.inj (targetAbuts.symm.trans sourceAbuts)
        subst targetVertex
        apply congrArg some
        refine Sigma.ext rfl ?_
        exact heq_of_eq <| by
          rw [← componentEquality]
          exact (finiteComponentEquiv_incidence diagram root object
            ⟨branch, vertex, targetAbuts⟩ component).symm

/-- The canonical finite-component comparison is injective on vertices. -/
theorem finiteComponentComparison_vertex_injective
    (root : diagram.base.Vertex) (object : diagram.GluedObject) :
    Function.Injective
      (finiteComponentComparison diagram root object).vertexMap := by
  rintro ⟨firstVertex, firstComponent⟩ ⟨secondVertex, secondComponent⟩ equality
  have vertexEquality : firstVertex = secondVertex :=
    Sigma.mk.inj_iff.mp equality |>.1
  subst secondVertex
  have componentEquality :
      finiteVertexComponentEquiv diagram root object firstVertex firstComponent =
        finiteVertexComponentEquiv diagram root object firstVertex secondComponent :=
    eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
  refine Sigma.ext rfl ?_
  exact heq_of_eq
    ((finiteVertexComponentEquiv diagram root object firstVertex).injective
      componentEquality)

/-- The canonical finite-component comparison is injective on edges. -/
theorem finiteComponentComparison_edge_injective
    (root : diagram.base.Vertex) (object : diagram.GluedObject) :
    Function.Injective
      (finiteComponentComparison diagram root object).edgeMap := by
  rintro ⟨firstEdge, firstComponent⟩ ⟨secondEdge, secondComponent⟩ equality
  have edgeEquality : firstEdge = secondEdge :=
    Sigma.mk.inj_iff.mp equality |>.1
  subst secondEdge
  have componentEquality :
      finiteEdgeComponentEquiv diagram root object firstEdge firstComponent =
        finiteEdgeComponentEquiv diagram root object firstEdge secondComponent :=
    eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
  refine Sigma.ext rfl ?_
  exact heq_of_eq
    ((finiteEdgeComponentEquiv diagram root object firstEdge).injective
      componentEquality)

/-- On vertices, the finite-component comparison intertwines the ordinary
finite-étale transition with the induced map of tempered components. -/
theorem finiteComponentComparison_vertex_naturality
    (root : diagram.base.Vertex)
    {source target : diagram.GluedObject} (map : source ⟶ target)
    (vertex :
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
        diagram root source).Vertex) :
    (finiteComponentComparison diagram root target).vertexMap
        ((SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
          diagram root map).vertexMap vertex) =
      (coverSemiGraphMap diagram root (finiteCovMap diagram root map)).vertexMap
        ((finiteComponentComparison diagram root source).vertexMap vertex) := by
  rcases vertex with ⟨vertex, component⟩
  refine Sigma.ext rfl ?_
  exact heq_of_eq
    (finiteVertexComponentEquiv_naturality
      diagram root map vertex component)

/-- On edges, the finite-component comparison intertwines the ordinary
finite-étale transition with the induced map of tempered components. -/
theorem finiteComponentComparison_edge_naturality
    (root : diagram.base.Vertex)
    {source target : diagram.GluedObject} (map : source ⟶ target)
    (edge :
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverSemiGraph
        diagram root source).Edge) :
    (finiteComponentComparison diagram root target).edgeMap
        ((SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
          diagram root map).edgeMap edge) =
      (coverSemiGraphMap diagram root (finiteCovMap diagram root map)).edgeMap
        ((finiteComponentComparison diagram root source).edgeMap edge) := by
  rcases edge with ⟨edge, component⟩
  refine Sigma.ext rfl ?_
  exact heq_of_eq
    (finiteEdgeComponentEquiv_naturality
      diagram root map edge component)

end SourceSemiGraphOfAnabelioids.CovObject

end Iut
