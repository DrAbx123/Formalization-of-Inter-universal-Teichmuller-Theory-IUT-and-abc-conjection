/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceGluedFiniteEtaleCover

/-!
# Functoriality of glued finite-etale semigraph covers

A morphism of objects of `B(G)` sends each constituent connected component
to a connected component.  These maps commute with every branch incidence,
and therefore assemble into the refinement morphism between the associated
finite-etale semigraphs.  Identity and composition are proved rather than
stored as extra transition data.
-/

namespace Iut

universe u

open CategoryTheory

namespace EtaleFundamentalGroup

/-- A morphism in a connected anabelioid maps connected components of its
source object to connected components of its target object. -/
noncomputable def fiberComponentHomMap
    (data : EtaleFundamentalGroup.{u})
    {source target : data.Cover}
    (morphism :
      letI := data.coverCategory
      source ⟶ target) :
    data.FiberComponent source → data.FiberComponent target := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  exact Quotient.map'
    (fun point => data.fiber.map morphism point)
    (fun firstPoint secondPoint relation => by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
      obtain ⟨automorphism, relation⟩ := relation
      refine ⟨automorphism, ?_⟩
      rw [← relation]
      have hnatural := ConcreteCategory.congr_hom
        (automorphism.hom.naturality morphism) secondPoint
      change
        automorphism • data.fiber.map morphism secondPoint =
          data.fiber.map morphism
            (automorphism • secondPoint) at hnatural
      exact hnatural)

/-- Component maps preserve identity morphisms. -/
theorem fiberComponentHomMap_id_apply
    (data : EtaleFundamentalGroup.{u})
    (object : data.Cover)
    (component : data.FiberComponent object) :
    fiberComponentHomMap data
        (letI := data.coverCategory; 𝟙 object) component = component := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  refine Quotient.inductionOn' component ?_
  intro point
  apply Quotient.sound
  change _ ∈ MulAction.orbit (Aut data.fiber) _
  simpa only [Functor.map_id_apply] using
    MulAction.mem_orbit_self (M := Aut data.fiber) point

/-- Component maps preserve composition. -/
theorem fiberComponentHomMap_comp_apply
    (data : EtaleFundamentalGroup.{u})
    {first second third : data.Cover}
    (firstMap :
      letI := data.coverCategory
      first ⟶ second)
    (secondMap :
      letI := data.coverCategory
      second ⟶ third)
    (component : data.FiberComponent first) :
    fiberComponentHomMap data
        (letI := data.coverCategory; firstMap ≫ secondMap) component =
      fiberComponentHomMap data secondMap
        (fiberComponentHomMap data firstMap component) := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  refine Quotient.inductionOn' component ?_
  intro point
  apply Quotient.sound
  change _ ∈ MulAction.orbit (Aut data.fiber) _
  simpa only [Functor.map_comp, FintypeCat.comp_apply] using
    MulAction.mem_orbit_self
      (M := Aut data.fiber) (data.fiber.map (firstMap ≫ secondMap) point)

/-- The map underlying component transport along an isomorphism is the
ordinary component map of its forward morphism. -/
theorem fiberComponentEquiv_apply
    (data : EtaleFundamentalGroup.{u})
    {source target : data.Cover}
    (identification :
      letI := data.coverCategory
      source ≅ target)
    (component : data.FiberComponent source) :
    letI := data.coverCategory
    (fiberComponentEquiv data identification).toFun component =
      fiberComponentHomMap data identification.hom component :=
  rfl

/-- Component transport through a pointed pullback is natural in the object. -/
theorem fiberComponentMap_naturality
    {source target : EtaleFundamentalGroup.{u}}
    (pointed : SourcePointedAnabelioidHom source target)
    {first second : target.Cover}
    (morphism :
      letI := target.coverCategory
      first ⟶ second)
    (component :
      source.FiberComponent
        (letI := target.coverCategory
         letI := source.coverCategory
         pointed.pullback.obj first)) :
    fiberComponentHomMap target morphism
        (fiberComponentMap pointed first component) =
      fiberComponentMap pointed second
        (fiberComponentHomMap source
          (letI := target.coverCategory
           letI := source.coverCategory
           pointed.pullback.map morphism) component) := by
  letI := target.coverCategory
  letI := source.coverCategory
  letI := target.galoisCategory
  letI := source.galoisCategory
  letI := target.fiberFunctor
  letI := source.fiberFunctor
  refine Quotient.inductionOn' component ?_
  intro point
  simp only [fiberComponentHomMap, fiberComponentMap,
    Quotient.map'_mk'']
  change
    @Eq
      (Quotient (MulAction.orbitRel (Aut target.fiber)
        (target.fiber.obj second)))
      (Quotient.mk''
        (target.fiber.map morphism
          (pointed.fiberIso.hom.app first point)))
      (Quotient.mk''
        (pointed.fiberIso.hom.app second
          (source.fiber.map (pointed.pullback.map morphism) point)))
  exact congrArg Quotient.mk''
    (ConcreteCategory.congr_hom
      (pointed.fiberIso.hom.naturality morphism) point).symm

end EtaleFundamentalGroup

namespace SourceSemiGraphOfAnabelioids.GluedObject

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)

section Transition

variable {source target : diagram.GluedObject}
    (morphism : source ⟶ target)

/-- The constituentwise map on vertices of finite-etale semigraphs. -/
noncomputable def finiteEtaleCoverVertexMap :
    CoverVertex diagram source → CoverVertex diagram target
  | ⟨vertex, component⟩ =>
      ⟨vertex, EtaleFundamentalGroup.fiberComponentHomMap
        (diagram.vertexAnabelioid vertex)
        (morphism.app vertex) component⟩

/-- The constituentwise map on edges of finite-etale semigraphs. -/
noncomputable def finiteEtaleCoverEdgeMap :
    CoverEdge diagram root source → CoverEdge diagram root target
  | ⟨edge, component⟩ => by
      let reference := coverReferenceBranch diagram root edge
      letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
      letI := (diagram.edgeAnabelioid edge).coverCategory
      exact ⟨edge, EtaleFundamentalGroup.fiberComponentHomMap
        (diagram.edgeAnabelioid edge)
        (reference.pullback.map (morphism.app reference.vertex)) component⟩

/-- Incidence is natural under a morphism of glued objects. -/
theorem coverComponentMap_naturality
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge)
    (component : CoverEdgeComponent diagram root source edge) :
    EtaleFundamentalGroup.fiberComponentHomMap
        (diagram.vertexAnabelioid branch.vertex)
        (morphism.app branch.vertex)
        (coverComponentMap diagram root source branch component) =
      coverComponentMap diagram root target branch
        (EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.edgeAnabelioid edge)
          (let reference := coverReferenceBranch diagram root edge
           letI :=
             (diagram.vertexAnabelioid reference.vertex).coverCategory
           letI := (diagram.edgeAnabelioid edge).coverCategory
           reference.pullback.map (morphism.app reference.vertex)) component) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid branch.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid reference.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.vertexAnabelioid branch.vertex).fiberFunctor
  letI := (diagram.vertexAnabelioid reference.vertex).fiberFunctor
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  rw [coverComponentMap, coverComponentMap]
  rw [EtaleFundamentalGroup.fiberComponentMap_naturality]
  apply congrArg
    (EtaleFundamentalGroup.fiberComponentMap
      (diagram.branchMorphism branch.branch branch.abuts)
      (target.vertexObject branch.vertex))
  rw [EtaleFundamentalGroup.fiberComponentEquiv_apply,
    EtaleFundamentalGroup.fiberComponentEquiv_apply]
  calc
    _ = EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.edgeAnabelioid edge)
          ((coverEdgeIdentification diagram root source branch).hom ≫
            (diagram.branchMorphism branch.branch branch.abuts).pullback.map
              (morphism.app branch.vertex)) component :=
      (EtaleFundamentalGroup.fiberComponentHomMap_comp_apply
        (diagram.edgeAnabelioid edge)
        (coverEdgeIdentification diagram root source branch).hom
        ((diagram.branchMorphism branch.branch branch.abuts).pullback.map
          (morphism.app branch.vertex)) component).symm
    _ = EtaleFundamentalGroup.fiberComponentHomMap
          (diagram.edgeAnabelioid edge)
          (reference.pullback.map (morphism.app reference.vertex) ≫
            (coverEdgeIdentification diagram root target branch).hom)
          component := congrArg
      (fun map => EtaleFundamentalGroup.fiberComponentHomMap
        (diagram.edgeAnabelioid edge) map component)
      (morphism.naturality reference branch)
    _ = _ := EtaleFundamentalGroup.fiberComponentHomMap_comp_apply
      (diagram.edgeAnabelioid edge)
      (reference.pullback.map (morphism.app reference.vertex))
      (coverEdgeIdentification diagram root target branch).hom component

/-- A morphism of glued finite-etale objects induces the corresponding
refinement morphism of their semigraphs. -/
noncomputable def finiteEtaleCoverTransition :
    (finiteEtaleCoverSemiGraph diagram root source).Hom
      (finiteEtaleCoverSemiGraph diagram root target) where
  vertexMap := finiteEtaleCoverVertexMap diagram morphism
  edgeMap := finiteEtaleCoverEdgeMap diagram root morphism
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    rintro ⟨edge, component⟩ branch ⟨vertex, vertexComponent⟩ coincidence
    cases abuts : diagram.base.coincidence edge branch with
    | none =>
        rw [finiteEtaleCoverSemiGraph_coincidence_of_none diagram root source
          abuts] at coincidence
        cases coincidence
    | some abuttingVertex =>
        rw [finiteEtaleCoverSemiGraph_coincidence_of_some diagram root source
          abuts] at coincidence
        have componentEquality := Option.some.inj coincidence
        cases componentEquality
        let reference := coverReferenceBranch diagram root edge
        letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
        letI := (diagram.edgeAnabelioid edge).coverCategory
        change (finiteEtaleCoverSemiGraph diagram root target).coincidence
          ⟨edge, EtaleFundamentalGroup.fiberComponentHomMap
            (diagram.edgeAnabelioid edge)
            (reference.pullback.map (morphism.app reference.vertex))
            component⟩ branch =
          some ⟨vertex,
            EtaleFundamentalGroup.fiberComponentHomMap
              (diagram.vertexAnabelioid vertex)
              (morphism.app vertex)
              (coverComponentMap diagram root source
                ⟨branch, vertex, abuts⟩ component)⟩
        rw [finiteEtaleCoverSemiGraph_coincidence_of_some diagram root target
          abuts]
        apply congrArg some
        refine Sigma.ext rfl ?_
        exact heq_of_eq
          (coverComponentMap_naturality diagram root morphism
            ⟨branch, vertex, abuts⟩ component).symm

/-- The vertex map induced by an identity morphism is the identity. -/
theorem finiteEtaleCoverVertexMap_id
    (object : diagram.GluedObject)
    (vertex : CoverVertex diagram object) :
    finiteEtaleCoverVertexMap diagram (𝟙 object) vertex = vertex := by
  rcases vertex with ⟨baseVertex, component⟩
  change (⟨baseVertex, _⟩ : CoverVertex diagram object) =
    ⟨baseVertex, component⟩
  refine Sigma.ext rfl ?_
  exact heq_of_eq
    (EtaleFundamentalGroup.fiberComponentHomMap_id_apply
      (diagram.vertexAnabelioid baseVertex)
      (object.vertexObject baseVertex) component)

/-- The edge map induced by an identity morphism is the identity. -/
theorem finiteEtaleCoverEdgeMap_id
    (object : diagram.GluedObject)
    (edge : CoverEdge diagram root object) :
    finiteEtaleCoverEdgeMap diagram root (𝟙 object) edge = edge := by
  rcases edge with ⟨baseEdge, component⟩
  let reference := coverReferenceBranch diagram root baseEdge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid baseEdge).coverCategory
  change (⟨baseEdge, _⟩ : CoverEdge diagram root object) =
    ⟨baseEdge, component⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change EtaleFundamentalGroup.fiberComponentHomMap
      (diagram.edgeAnabelioid baseEdge)
      (reference.pullback.map (𝟙 (object.vertexObject reference.vertex)))
      component = component
  have mapIdentity :
      reference.pullback.map (𝟙 (object.vertexObject reference.vertex)) =
        𝟙 (reference.pullback.obj (object.vertexObject reference.vertex)) :=
    reference.pullback.map_id _
  rw [mapIdentity]
  exact EtaleFundamentalGroup.fiberComponentHomMap_id_apply
    (diagram.edgeAnabelioid baseEdge)
    (coverEdgeObject diagram root object baseEdge) component

/-- Vertex refinement maps respect composition. -/
theorem finiteEtaleCoverVertexMap_comp
    {first middle target : diagram.GluedObject}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ target)
    (vertex : CoverVertex diagram first) :
    finiteEtaleCoverVertexMap diagram (firstMap ≫ secondMap) vertex =
      finiteEtaleCoverVertexMap diagram secondMap
        (finiteEtaleCoverVertexMap diagram firstMap vertex) := by
  rcases vertex with ⟨baseVertex, component⟩
  change (⟨baseVertex, _⟩ : CoverVertex diagram target) =
    ⟨baseVertex, _⟩
  refine Sigma.ext rfl ?_
  exact heq_of_eq
    (EtaleFundamentalGroup.fiberComponentHomMap_comp_apply
      (diagram.vertexAnabelioid baseVertex)
      (firstMap.app baseVertex) (secondMap.app baseVertex) component)

/-- Edge refinement maps respect composition. -/
theorem finiteEtaleCoverEdgeMap_comp
    {first middle target : diagram.GluedObject}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ target)
    (edge : CoverEdge diagram root first) :
    finiteEtaleCoverEdgeMap diagram root (firstMap ≫ secondMap) edge =
      finiteEtaleCoverEdgeMap diagram root secondMap
        (finiteEtaleCoverEdgeMap diagram root firstMap edge) := by
  rcases edge with ⟨baseEdge, component⟩
  let reference := coverReferenceBranch diagram root baseEdge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid baseEdge).coverCategory
  change (⟨baseEdge, _⟩ : CoverEdge diagram root target) =
    ⟨baseEdge, _⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change EtaleFundamentalGroup.fiberComponentHomMap
      (diagram.edgeAnabelioid baseEdge)
      (reference.pullback.map
        (firstMap.app reference.vertex ≫ secondMap.app reference.vertex))
      component = _
  rw [Functor.map_comp]
  exact EtaleFundamentalGroup.fiberComponentHomMap_comp_apply
    (diagram.edgeAnabelioid baseEdge)
    (reference.pullback.map (firstMap.app reference.vertex))
    (reference.pullback.map (secondMap.app reference.vertex)) component

/-- Finite-étale transitions respect composition as complete semi-graph
morphisms, including their dependent branch equivalences. -/
theorem finiteEtaleCoverTransition_comp
    {first middle target : diagram.GluedObject}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ target) :
    finiteEtaleCoverTransition diagram root (firstMap ≫ secondMap) =
      (finiteEtaleCoverTransition diagram root firstMap).comp
        (finiteEtaleCoverTransition diagram root secondMap) := by
  apply SourceSemiGraph.Hom.ext
  · exact finiteEtaleCoverVertexMap_comp diagram firstMap secondMap
  · exact finiteEtaleCoverEdgeMap_comp diagram root firstMap secondMap
  · intro edge branch
    rfl

/-- Every finite-etale refinement lies over the identity of the original
base semigraph on vertices. -/
theorem finiteEtaleCoverTransition_vertex_over_base
    (vertex : CoverVertex diagram source) :
    (finiteEtaleCoverProjection diagram root target).vertexMap
        ((finiteEtaleCoverTransition diagram root morphism).vertexMap vertex) =
      (finiteEtaleCoverProjection diagram root source).vertexMap vertex :=
  rfl

/-- Every finite-etale refinement lies over the identity of the original
base semigraph on edges. -/
theorem finiteEtaleCoverTransition_edge_over_base
    (edge : CoverEdge diagram root source) :
    (finiteEtaleCoverProjection diagram root target).edgeMap
        ((finiteEtaleCoverTransition diagram root morphism).edgeMap edge) =
      (finiteEtaleCoverProjection diagram root source).edgeMap edge :=
  rfl

/-- Refinement maps do not alter the branch label over the base semigraph. -/
theorem finiteEtaleCoverTransition_branch_over_base
    (edge : CoverEdge diagram root source)
    (branch : (finiteEtaleCoverSemiGraph diagram root source).Branch edge) :
    (finiteEtaleCoverProjection diagram root target).branchEquiv
        ((finiteEtaleCoverTransition diagram root morphism).edgeMap edge)
        ((finiteEtaleCoverTransition diagram root morphism).branchEquiv
          edge branch) =
      (finiteEtaleCoverProjection diagram root source).branchEquiv edge branch :=
  rfl

/-- Every morphism of glued finite-etale objects induces a proper semigraph
refinement: it preserves whether each branch is verticial. -/
theorem finiteEtaleCoverTransition_isProper :
    (finiteEtaleCoverTransition diagram root morphism).IsProper := by
  intro edge branch
  rcases edge with ⟨baseEdge, component⟩
  cases abuts : diagram.base.coincidence baseEdge branch with
  | none =>
      constructor
      · rintro ⟨vertex, sourceCoincidence⟩
        rw [finiteEtaleCoverSemiGraph_coincidence_of_none
          diagram root source abuts] at sourceCoincidence
        cases sourceCoincidence
      · rintro ⟨vertex, targetCoincidence⟩
        have mapped :=
          (finiteEtaleCoverProjection diagram root target).map_coincidence
            ((finiteEtaleCoverTransition diagram root morphism).edgeMap
              ⟨baseEdge, component⟩)
            ((finiteEtaleCoverTransition diagram root morphism).branchEquiv
              ⟨baseEdge, component⟩ branch)
            vertex targetCoincidence
        change diagram.base.coincidence baseEdge branch = some _ at mapped
        rw [abuts] at mapped
        cases mapped
  | some vertex =>
      constructor <;> intro _
      · exact ⟨⟨vertex, coverComponentMap diagram root target
          ⟨branch, vertex, abuts⟩
          ((finiteEtaleCoverEdgeMap diagram root morphism)
            ⟨baseEdge, component⟩).2⟩,
          finiteEtaleCoverSemiGraph_coincidence_of_some
            diagram root target abuts⟩
      · exact ⟨⟨vertex, coverComponentMap diagram root source
          ⟨branch, vertex, abuts⟩ component⟩,
          finiteEtaleCoverSemiGraph_coincidence_of_some
            diagram root source abuts⟩

end Transition

end SourceSemiGraphOfAnabelioids.GluedObject

end Iut
