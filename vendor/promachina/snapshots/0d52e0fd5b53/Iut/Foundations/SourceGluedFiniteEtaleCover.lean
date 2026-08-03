/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceGluedGalois
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Finite-etale semigraph covers of a glued anabelioid

For `S : B(G)`, Definition 2.1 constructs a semigraph over `G` whose vertices
and edges are the connected components of the restrictions of `S` to the
corresponding constituent anabelioids.  Connected components are represented
canonically as orbits of the automorphism group of the chosen constituent
fiber functor.  This file constructs the underlying semigraph and its proper
finite-component projection without adding any covering data as fields.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace EtaleFundamentalGroup

/-- Connected components of an object of a connected anabelioid, represented
as the orbit set of its fiber under the automorphism group of the fiber
functor. -/
abbrev FiberComponent (data : EtaleFundamentalGroup.{u})
    (object : data.Cover) : Type u :=
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  MulAction.orbitRel.Quotient (Aut data.fiber) (data.fiber.obj object)

noncomputable instance fiberComponentFintype
    (data : EtaleFundamentalGroup.{u}) (object : data.Cover) :
    Fintype (data.FiberComponent object) := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  exact Fintype.ofFinite _

/-- An isomorphism of objects induces the canonical bijection of connected
components. -/
noncomputable def fiberComponentEquiv
    (data : EtaleFundamentalGroup.{u})
    {first second : data.Cover}
    (identification :
      letI := data.coverCategory
      first ≅ second) :
    data.FiberComponent first ≃ data.FiberComponent second := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  let forward : data.FiberComponent first → data.FiberComponent second :=
    Quotient.map' (fun point => data.fiber.map identification.hom point)
      (fun firstPoint secondPoint relation => by
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
        obtain ⟨automorphism, relation⟩ := relation
        refine ⟨automorphism, ?_⟩
        rw [← relation]
        simpa only [FintypeCat.comp_apply] using
          ConcreteCategory.congr_hom
            (automorphism.hom.naturality identification.hom) secondPoint)
  let reverse : data.FiberComponent second → data.FiberComponent first :=
    Quotient.map' (fun point => data.fiber.map identification.inv point)
      (fun firstPoint secondPoint relation => by
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
        obtain ⟨automorphism, relation⟩ := relation
        refine ⟨automorphism, ?_⟩
        rw [← relation]
        simpa only [FintypeCat.comp_apply] using
          ConcreteCategory.congr_hom
            (automorphism.hom.naturality identification.inv) secondPoint)
  exact
    { toFun := forward
      invFun := reverse
      left_inv := by
        intro component
        refine Quotient.inductionOn' component ?_
        intro point
        apply Quotient.sound
        change _ ∈ MulAction.orbit (Aut data.fiber) _
        simpa only [← FintypeCat.comp_apply, ← Functor.map_comp,
          identification.hom_inv_id, Functor.map_id_apply] using
            MulAction.mem_orbit_self (M := Aut data.fiber) point
      right_inv := by
        intro component
        refine Quotient.inductionOn' component ?_
        intro point
        apply Quotient.sound
        change _ ∈ MulAction.orbit (Aut data.fiber) _
        simpa only [← FintypeCat.comp_apply, ← Functor.map_comp,
          identification.inv_hom_id, Functor.map_id_apply] using
            MulAction.mem_orbit_self (M := Aut data.fiber) point }

/-- A pointed exact morphism maps connected components of a pulled-back
object to connected components of the original object. -/
noncomputable def fiberComponentMap
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourcePointedAnabelioidHom source target)
    (object : target.Cover) :
    source.FiberComponent
        (letI := target.coverCategory
         letI := source.coverCategory
         morphism.pullback.obj object) →
      target.FiberComponent object := by
  letI := target.coverCategory
  letI := source.coverCategory
  letI := target.galoisCategory
  letI := source.galoisCategory
  letI := target.fiberFunctor
  letI := source.fiberFunctor
  exact Quotient.map'
    (fun point => morphism.fiberIso.hom.app object point)
    (fun firstPoint secondPoint relation => by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
      obtain ⟨automorphism, relation⟩ := relation
      refine ⟨morphism.fiberAutHom automorphism, ?_⟩
      rw [morphism.fiberIso_equivariant]
      exact congrArg (fun point => morphism.fiberIso.hom.app object point)
        relation)

end EtaleFundamentalGroup

namespace SourceSemiGraphOfAnabelioids.GluedObject

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})

section VerticialCover

variable (root : diagram.base.Vertex)
    (object : diagram.GluedObject)

/-- A chosen incident branch on each edge.  Connectedness and the chosen root
place us in the verticial case, where every edge abuts at least one vertex. -/
noncomputable def coverReferenceBranch
    (edge : diagram.base.Edge) : diagram.IncidentBranch edge := by
  letI : Nonempty diagram.base.Vertex := ⟨root⟩
  let witness :=
    diagram.connected.edge_abuts_of_nonempty (G := diagram.base) edge
  let vertex := Classical.choose witness
  let branchWitness := Classical.choose_spec witness
  let branch := Classical.choose branchWitness
  let abuts := Classical.choose_spec branchWitness
  exact ⟨branch, vertex, abuts⟩

/-- Connected components of the restriction of `object` to a vertex. -/
abbrev CoverVertexComponent (vertex : diagram.base.Vertex) : Type u :=
  (diagram.vertexAnabelioid vertex).FiberComponent
    (object.vertexObject vertex)

/-- The edge restriction, represented using the chosen incident branch. -/
noncomputable def coverEdgeObject (edge : diagram.base.Edge) :
    (diagram.edgeAnabelioid edge).Cover := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact reference.pullback.obj (object.vertexObject reference.vertex)

/-- Connected components of the restriction of `object` to an edge. -/
abbrev CoverEdgeComponent (edge : diagram.base.Edge) : Type u :=
  (diagram.edgeAnabelioid edge).FiberComponent
    (coverEdgeObject diagram root object edge)

/-- Transport the chosen edge representative to the pullback at an arbitrary
incident branch. -/
noncomputable def coverEdgeIdentification
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid
      (coverReferenceBranch diagram root edge).vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    coverEdgeObject diagram root object edge ≅
      branch.pullback.obj (object.vertexObject branch.vertex) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact object.glue reference branch

/-- Incidence on connected components: transport from the reference edge
restriction to the displayed branch and then use the pointed branch fiber
comparison. -/
noncomputable def coverComponentMap
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    CoverEdgeComponent diagram root object edge →
      CoverVertexComponent diagram object branch.vertex :=
  fun component =>
    EtaleFundamentalGroup.fiberComponentMap
        (diagram.branchMorphism branch.branch branch.abuts)
        (object.vertexObject branch.vertex)
      ((EtaleFundamentalGroup.fiberComponentEquiv
        (diagram.edgeAnabelioid edge)
        (coverEdgeIdentification diagram root object branch)).toFun component)

/-- Vertices of the finite-etale semigraph attached to `object`. -/
abbrev CoverVertex : Type u :=
  Σ vertex, CoverVertexComponent diagram object vertex

/-- Edges of the finite-etale semigraph attached to `object`. -/
abbrev CoverEdge : Type u :=
  Σ edge, CoverEdgeComponent diagram root object edge

/-- The underlying semigraph `G^S` of the finite-etale covering represented
by `object : B(G)`. -/
noncomputable def finiteEtaleCoverSemiGraph : SourceSemiGraph.{u} where
  Vertex := CoverVertex diagram object
  Edge := CoverEdge diagram root object
  Branch := fun edge => diagram.base.Branch edge.1
  branchFintype := fun edge => diagram.base.branchFintype edge.1
  branch_card := fun edge => diagram.base.branch_card edge.1
  coincidence := fun edge branch =>
    match abuts : diagram.base.coincidence edge.1 branch with
    | none => none
    | some vertex =>
        some ⟨vertex,
          coverComponentMap diagram root object
            ⟨branch, vertex, abuts⟩ edge.2⟩

/-- The defining incidence formula for the finite-etale cover semigraph. -/
theorem finiteEtaleCoverSemiGraph_coincidence
    (edge : diagram.base.Edge)
    (component : CoverEdgeComponent diagram root object edge)
    (branch : diagram.base.Branch edge) :
    (finiteEtaleCoverSemiGraph diagram root object).coincidence
        ⟨edge, component⟩ branch =
      match abuts : diagram.base.coincidence edge branch with
      | none => none
      | some vertex =>
          some ⟨vertex, coverComponentMap diagram root object
            ⟨branch, vertex, abuts⟩ component⟩ :=
  rfl

@[simp]
theorem finiteEtaleCoverSemiGraph_coincidence_of_some
    {edge : diagram.base.Edge}
    {component : CoverEdgeComponent diagram root object edge}
    {branch : diagram.base.Branch edge}
    {vertex : diagram.base.Vertex}
    (abuts : diagram.base.coincidence edge branch = some vertex) :
    (finiteEtaleCoverSemiGraph diagram root object).coincidence
        ⟨edge, component⟩ branch =
      some ⟨vertex, coverComponentMap diagram root object
        ⟨branch, vertex, abuts⟩ component⟩ := by
  rw [finiteEtaleCoverSemiGraph_coincidence]
  split
  next noVertex =>
    have impossible : (none : Option diagram.base.Vertex) = some vertex :=
      noVertex.symm.trans abuts
    cases impossible
  next actualVertex actual =>
    have vertexEquality : actualVertex = vertex :=
      Option.some.inj (actual.symm.trans abuts)
    subst actualVertex
    rfl

@[simp]
theorem finiteEtaleCoverSemiGraph_coincidence_of_none
    {edge : diagram.base.Edge}
    {component : CoverEdgeComponent diagram root object edge}
    {branch : diagram.base.Branch edge}
    (noVertex : diagram.base.coincidence edge branch = none) :
    (finiteEtaleCoverSemiGraph diagram root object).coincidence
        ⟨edge, component⟩ branch = none := by
  rw [finiteEtaleCoverSemiGraph_coincidence]
  split
  next _ => rfl
  next vertex abuts =>
    have impossible : some vertex = (none : Option diagram.base.Vertex) :=
      abuts.symm.trans noVertex
    cases impossible

/-- The proper morphism of semigraphs underlying the finite-etale cover. -/
noncomputable def finiteEtaleCoverProjection :
    (finiteEtaleCoverSemiGraph diagram root object).Hom diagram.base where
  vertexMap := Sigma.fst
  edgeMap := Sigma.fst
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro liftedEdge branch liftedVertex coincidence
    rcases liftedEdge with ⟨edge, component⟩
    rcases liftedVertex with ⟨vertex, vertexComponent⟩
    change (finiteEtaleCoverSemiGraph diagram root object).coincidence
      ⟨edge, component⟩ branch = some ⟨vertex, vertexComponent⟩ at coincidence
    change diagram.base.coincidence edge branch = some vertex
    rw [finiteEtaleCoverSemiGraph_coincidence] at coincidence
    split at coincidence
    · cases coincidence
    · next abuttingVertex abuts =>
        have vertexEquality : abuttingVertex = vertex :=
          Sigma.mk.inj_iff.mp (Option.some.inj coincidence) |>.1
        exact abuts.trans (congrArg some vertexEquality)

/-- The projection is proper: a branch is verticial upstairs exactly when
its underlying branch is verticial downstairs. -/
theorem finiteEtaleCoverProjection_isProper :
    (finiteEtaleCoverProjection diagram root object).IsProper := by
  intro edge branch
  rcases edge with ⟨edge, component⟩
  constructor
  · rintro ⟨liftedVertex, coincidence⟩
    cases abuts : diagram.base.coincidence edge branch with
    | none =>
        rw [finiteEtaleCoverSemiGraph_coincidence_of_none diagram root object
          abuts] at coincidence
        cases coincidence
    | some vertex => exact ⟨vertex, abuts⟩
  · rintro ⟨vertex, abuts⟩
    change diagram.base.coincidence edge branch = some vertex at abuts
    exact ⟨⟨vertex, coverComponentMap diagram root object
      ⟨branch, vertex, abuts⟩ component⟩,
      finiteEtaleCoverSemiGraph_coincidence_of_some diagram root object abuts⟩

/-- Every vertex fiber of the finite-etale projection is finite. -/
noncomputable instance finiteEtaleCoverVertexFiberFinite
    (vertex : diagram.base.Vertex) :
    Finite ((finiteEtaleCoverProjection diagram root object).VertexFiber vertex) := by
  let equivalence :
      (finiteEtaleCoverProjection diagram root object).VertexFiber vertex ≃
      CoverVertexComponent diagram object vertex :=
    { toFun := fun point => by
        rcases point with ⟨⟨baseVertex, component⟩, equality⟩
        change baseVertex = vertex at equality
        subst baseVertex
        exact component
      invFun := fun component => ⟨⟨vertex, component⟩, rfl⟩
      left_inv := fun point => by
        rcases point with ⟨⟨baseVertex, component⟩, equality⟩
        change baseVertex = vertex at equality
        subst baseVertex
        rfl
      right_inv := fun _ => rfl }
  exact Finite.of_equiv _ equivalence.symm

/-- Every edge fiber of the finite-etale projection is finite. -/
noncomputable instance finiteEtaleCoverEdgeFiberFinite
    (edge : diagram.base.Edge) :
    Finite ((finiteEtaleCoverProjection diagram root object).EdgeFiber edge) := by
  let equivalence :
      (finiteEtaleCoverProjection diagram root object).EdgeFiber edge ≃
      CoverEdgeComponent diagram root object edge :=
    { toFun := fun point => by
        rcases point with ⟨⟨baseEdge, component⟩, equality⟩
        change baseEdge = edge at equality
        subst baseEdge
        exact component
      invFun := fun component => ⟨⟨edge, component⟩, rfl⟩
      left_inv := fun point => by
        rcases point with ⟨⟨baseEdge, component⟩, equality⟩
        change baseEdge = edge at equality
        subst baseEdge
        rfl
      right_inv := fun _ => rfl }
  exact Finite.of_equiv _ equivalence.symm

end VerticialCover

end SourceSemiGraphOfAnabelioids.GluedObject

end Iut
