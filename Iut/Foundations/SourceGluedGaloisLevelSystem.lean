/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceGluedConnectedFiniteEtaleCover
import Iut.Foundations.SourceConnectedAnabelioidSlice
import Iut.Foundations.SourceSemiGraphAction
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Galois.Topology

/-!
# The connected finite-etale Galois level system of a glued anabelioid

Immediately before Proposition 3.6 of *Semi-graphs of Anabelioids*, the
source chooses a cofinal system of pointed connected finite-etale Galois
objects of `B(G)`.  This file packages that system in the literal glued
category, attaches the finite-etale semigraph already constructed from each
object, and derives its connectedness and refinement maps.

No semigraph, connectedness, deck-group, or transition datum is accepted as
an input field.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace SourceSemiGraphOfAnabelioids.GluedObject

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)

/-- A pointed connected finite-etale Galois object of the literal category
`B(G)`.  The Galois proof is a property of the chosen object, not output
semigraph data. -/
structure GaloisLevel where
  object : diagram.GluedObject
  point : (rootFiber diagram root).obj object
  isGalois :
    letI : GaloisCategory diagram.GluedObject := galoisCategory diagram root
    PreGaloisCategory.IsGalois object

namespace GaloisLevel

/-- Point-preserving morphisms between Galois levels. -/
@[ext]
structure Hom (finer coarser : GaloisLevel diagram root) where
  val : finer.object ⟶ coarser.object
  comp : (rootFiber diagram root).map val finer.point = coarser.point := by simp

instance : Category (GaloisLevel diagram root) where
  Hom := Hom diagram root
  id level := ⟨𝟙 level.object, by simp⟩
  comp first second := ⟨first.val ≫ second.val, by
    simp only [Functor.map_comp, FintypeCat.comp_apply, first.comp, second.comp]⟩

@[simp]
theorem id_val (level : GaloisLevel diagram root) :
    (𝟙 level : level ⟶ level).val = 𝟙 level.object := rfl

@[simp]
theorem comp_val {first middle last : GaloisLevel diagram root}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    (f ≫ g).val = f.val ≫ g.val := rfl

/-- The finite-etale semigraph `G^i` attached to a Galois level. -/
noncomputable abbrev semiGraph
    (level : GaloisLevel diagram root) : SourceSemiGraph.{u} :=
  finiteEtaleCoverSemiGraph diagram root level.object

/-- The finite-etale projection `G^i → G`. -/
noncomputable abbrev projection
    (level : GaloisLevel diagram root) :
    level.semiGraph.Hom diagram.base :=
  finiteEtaleCoverProjection diagram root level.object

/-- The point of a pointed Galois object selects a vertex above the chosen
root of the base semigraph. -/
noncomputable def rootVertex
    (level : GaloisLevel diagram root) : level.semiGraph.Vertex :=
  ⟨root, Quotient.mk'' level.point⟩

/-- Every Galois level is connected because its underlying object of `B(G)`
is connected; this is the source-derived theorem proved in the preceding
module. -/
theorem semiGraph_connected
    (level : GaloisLevel diagram root) : level.semiGraph.IsConnected := by
  letI : GaloisCategory diagram.GluedObject := galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  exact finiteEtaleCoverSemiGraph_isConnected_of_isConnected
    diagram root level.object

/-- The projection of every Galois level is proper. -/
theorem projection_isProper
    (level : GaloisLevel diagram root) : level.projection.IsProper :=
  finiteEtaleCoverProjection_isProper diagram root level.object

/-- A morphism of pointed Galois objects induces the source's refinement map
between their finite-etale semigraphs. -/
noncomputable def transition
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    finer.semiGraph.Hom coarser.semiGraph :=
  finiteEtaleCoverTransition diagram root refinement.val

/-- Galois-level refinement lies over the identity of the base on vertices. -/
theorem transition_vertex_over_base
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (vertex : finer.semiGraph.Vertex) :
    coarser.projection.vertexMap
        ((transition diagram root refinement).vertexMap vertex) =
      finer.projection.vertexMap vertex :=
  finiteEtaleCoverTransition_vertex_over_base
    diagram root refinement.val vertex

/-- Galois-level refinement lies over the identity of the base on edges. -/
theorem transition_edge_over_base
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (edge : finer.semiGraph.Edge) :
    coarser.projection.edgeMap
        ((transition diagram root refinement).edgeMap edge) =
      finer.projection.edgeMap edge :=
  finiteEtaleCoverTransition_edge_over_base
    diagram root refinement.val edge

/-- The distinguished lifted root is preserved by pointed refinement. -/
theorem transition_rootVertex
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    (transition diagram root refinement).vertexMap finer.rootVertex =
      coarser.rootVertex := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  change
    (⟨root, EtaleFundamentalGroup.fiberComponentHomMap
      (diagram.vertexAnabelioid root)
      (refinement.val.app root) (Quotient.mk'' finer.point)⟩ :
        CoverVertex diagram coarser.object) =
      ⟨root, Quotient.mk'' coarser.point⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change Quotient.mk''
      ((diagram.vertexAnabelioid root).fiber.map
        (refinement.val.app root) finer.point) =
    Quotient.mk'' coarser.point
  exact congrArg Quotient.mk'' refinement.comp

/-- Refinement of Galois levels is proper. -/
theorem transition_isProper
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    (transition diagram root refinement).IsProper :=
  finiteEtaleCoverTransition_isProper diagram root refinement.val

/-- Galois-level transition is functorial on vertices. -/
theorem transition_vertex_comp
    {first middle last : GaloisLevel diagram root}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last)
    (vertex : first.semiGraph.Vertex) :
    (transition diagram root (firstMap ≫ secondMap)).vertexMap vertex =
      (transition diagram root secondMap).vertexMap
        ((transition diagram root firstMap).vertexMap vertex) :=
  finiteEtaleCoverVertexMap_comp diagram
    firstMap.val secondMap.val vertex

/-- Galois-level transition is functorial on edges. -/
theorem transition_edge_comp
    {first middle last : GaloisLevel diagram root}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last)
    (edge : first.semiGraph.Edge) :
    (transition diagram root (firstMap ≫ secondMap)).edgeMap edge =
      (transition diagram root secondMap).edgeMap
        ((transition diagram root firstMap).edgeMap edge) :=
  finiteEtaleCoverEdgeMap_comp diagram root
    firstMap.val secondMap.val edge

/-- Galois-level transitions respect composition as complete semi-graph
morphisms, including their dependent branch equivalences. -/
theorem transition_comp
    {first middle last : GaloisLevel diagram root}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last) :
    transition diagram root (firstMap ≫ secondMap) =
      (transition diagram root firstMap).comp
        (transition diagram root secondMap) := by
  apply SourceSemiGraph.Hom.ext
  · exact transition_vertex_comp diagram root firstMap secondMap
  · exact transition_edge_comp diagram root firstMap secondMap
  · intro edge branch
    rfl

/-- Identity refinement acts identically on vertices. -/
theorem transition_vertex_id
    (level : GaloisLevel diagram root)
    (vertex : level.semiGraph.Vertex) :
    (transition diagram root (𝟙 level)).vertexMap vertex = vertex :=
  finiteEtaleCoverVertexMap_id diagram level.object vertex

/-- Identity refinement acts identically on edges. -/
theorem transition_edge_id
    (level : GaloisLevel diagram root)
    (edge : level.semiGraph.Edge) :
    (transition diagram root (𝟙 level)).edgeMap edge = edge :=
  finiteEtaleCoverEdgeMap_id diagram root level.object edge

/-- Identity refinement induces the identity complete semi-graph morphism. -/
theorem transition_id
    (level : GaloisLevel diagram root) :
    transition diagram root (𝟙 level) = SourceSemiGraph.Hom.id level.semiGraph := by
  apply SourceSemiGraph.Hom.ext
  · exact transition_vertex_id diagram root level
  · exact transition_edge_id diagram root level
  · intro edge branch
    rfl

/-- Every connected finite-etale object, with a selected point, is dominated
by a pointed Galois level.  Thus the complete pointed-Galois indexing category
is cofinal for the use made immediately before Proposition 3.6. -/
theorem exists_galoisLevel_over_connected
    (object : diagram.GluedObject)
    [PreGaloisCategory.IsConnected object]
    (point : (rootFiber diagram root).obj object) :
    ∃ (level : GaloisLevel diagram root) (morphism : level.object ⟶ object),
      (rootFiber diagram root).map morphism level.point = point := by
  letI : GaloisCategory diagram.GluedObject := galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  obtain ⟨galoisObject, morphism, galoisPoint,
      isGalois, pointMaps⟩ :=
    PreGaloisCategory.exists_hom_from_galois_of_fiber
      (rootFiber diagram root) object point
  exact ⟨⟨galoisObject, galoisPoint, isGalois⟩, morphism, pointMaps⟩

/-- A pointed refinement between two levels is unique. -/
theorem refinement_unique
    {finer coarser : GaloisLevel diagram root}
    (first second : finer ⟶ coarser) : first = second := by
  apply GaloisLevel.Hom.ext
  letI : GaloisCategory diagram.GluedObject := galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  apply PreGaloisCategory.evaluation_injective_of_isConnected
    (rootFiber diagram root) finer.object coarser.object finer.point
  exact first.comp.trans second.comp.symm

/-- Pointed connected Galois levels form the cofiltered refinement system
chosen immediately before Proposition 3.6.  Common refinements and equalizers
are constructed in `B(G)` by the Galois-category operations. -/
noncomputable instance isCofilteredOrEmpty :
    IsCofilteredOrEmpty (GaloisLevel diagram root) where
  cone_objs := fun first second => by
    letI : GaloisCategory diagram.GluedObject :=
      galoisCategory diagram root
    letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
      rootFiberFunctor diagram root
    obtain ⟨common, morphism, point, isGalois, pointMaps⟩ :=
      PreGaloisCategory.exists_hom_from_galois_of_fiber
        (rootFiber diagram root) (first.object ⨯ second.object)
        ((PreGaloisCategory.fiberBinaryProductEquiv
          (rootFiber diagram root) first.object second.object).symm
            (first.point, second.point))
    refine ⟨⟨common, point, isGalois⟩,
      ⟨morphism ≫ prod.fst, ?_⟩, ⟨morphism ≫ prod.snd, ?_⟩, trivial⟩
    · simp only [Functor.map_comp, pointMaps, FintypeCat.comp_apply,
        PreGaloisCategory.fiberBinaryProductEquiv_symm_fst_apply]
    · simp only [Functor.map_comp, pointMaps, FintypeCat.comp_apply,
        PreGaloisCategory.fiberBinaryProductEquiv_symm_snd_apply]
  cone_maps := fun {first second} firstMap secondMap => by
    letI : GaloisCategory diagram.GluedObject :=
      galoisCategory diagram root
    letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
      rootFiberFunctor diagram root
    obtain ⟨common, morphism, point, isGalois, pointMaps⟩ :=
      PreGaloisCategory.exists_hom_from_galois_of_fiber
        (rootFiber diagram root) first.object first.point
    let commonLevel : GaloisLevel diagram root :=
      ⟨common, point, isGalois⟩
    let commonMap : commonLevel ⟶ first := ⟨morphism, pointMaps⟩
    exact ⟨commonLevel, commonMap,
      refinement_unique diagram root
        (commonMap ≫ firstMap) (commonMap ≫ secondMap)⟩

/-- The Galois-level refinement system is inhabited: the terminal object of
`B(G)` is connected and is dominated by a pointed Galois object. -/
noncomputable instance level_nonempty :
    Nonempty (GaloisLevel diagram root) := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  let terminalObject := ⊤_ diagram.GluedObject
  letI : PreGaloisCategory.IsConnected terminalObject :=
    sourceGaloisCategory_isConnected_of_isTerminal
      terminalObject (terminalIsTerminal)
  let point := Classical.choice
    (inferInstance : Nonempty ((rootFiber diagram root).obj terminalObject))
  obtain ⟨level, _morphism, _pointMaps⟩ :=
    exists_galoisLevel_over_connected diagram root terminalObject point
  exact ⟨level⟩

/-- Hence the selected level category is genuinely cofiltered, not merely
cofiltered when nonempty. -/
noncomputable instance isCofiltered :
    IsCofiltered (GaloisLevel diagram root) where
  cone_objs := IsCofilteredOrEmpty.cone_objs
  cone_maps := IsCofilteredOrEmpty.cone_maps
  nonempty := inferInstance

/-! ## The normal-open quotient represented by a Galois level -/

/-- The selected point of a Galois level has an open normal stabilizer in
the fundamental group `Aut(rootFiber)`.  This is the normal-open subgroup
whose coset quotient is represented by the finite Galois object. -/
noncomputable def openNormalStabilizer
    (level : GaloisLevel diagram root) :
    OpenNormalSubgroup (Aut (rootFiber diagram root)) := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  letI : TopologicalSpace ((rootFiber diagram root).obj level.object) := ⊥
  letI : DiscreteTopology ((rootFiber diagram root).obj level.object) :=
    ⟨rfl⟩
  exact
    { toOpenSubgroup :=
        { toSubgroup := MulAction.stabilizer
            (Aut (rootFiber diagram root)) level.point
          isOpen' := stabilizer_isOpen
            (Aut (rootFiber diagram root)) level.point }
      isNormal' := PreGaloisCategory.stabilizer_normal_of_isGalois
        (rootFiber diagram root) level.object level.point }

/-- The fiber of a connected Galois level is exactly the normal-open coset
set of its point stabilizer.  This identifies the categorical levels used
here with the existing coset formulas, without taking a subgroup diagram as
an independent input. -/
noncomputable def fiberCosetEquiv
    (level : GaloisLevel diagram root) :
    Aut (rootFiber diagram root) ⧸
        (level.openNormalStabilizer : Subgroup (Aut (rootFiber diagram root))) ≃
      (rootFiber diagram root).obj level.object := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  letI : MulAction.IsPretransitive
      (Aut (rootFiber diagram root))
      ((rootFiber diagram root).obj level.object) :=
    PreGaloisCategory.FiberFunctor.isPretransitive_of_isGalois
      (rootFiber diagram root) level.object
  exact
    (MulAction.orbitEquivQuotientStabilizer
      (Aut (rootFiber diagram root)) level.point).symm |>.trans
      ((Equiv.setCongr
        (MulAction.orbit_eq_univ
          (Aut (rootFiber diagram root)) level.point)).trans
        (Equiv.Set.univ ((rootFiber diagram root).obj level.object)))

/-! ## The finite Galois deck action -/

/-- An automorphism of the Galois object permutes the vertices of its
associated finite-etale semigraph. -/
noncomputable def automorphismVertexPerm
    (level : GaloisLevel diagram root) (automorphism : Aut level.object) :
    Equiv.Perm level.semiGraph.Vertex where
  toFun := finiteEtaleCoverVertexMap diagram automorphism.hom
  invFun := finiteEtaleCoverVertexMap diagram automorphism.inv
  left_inv vertex := by
    rw [← finiteEtaleCoverVertexMap_comp diagram
      automorphism.hom automorphism.inv vertex,
      automorphism.hom_inv_id]
    exact finiteEtaleCoverVertexMap_id diagram level.object vertex
  right_inv vertex := by
    rw [← finiteEtaleCoverVertexMap_comp diagram
      automorphism.inv automorphism.hom vertex,
      automorphism.inv_hom_id]
    exact finiteEtaleCoverVertexMap_id diagram level.object vertex

/-- The vertex permutations form the finite-level deck action. -/
noncomputable def automorphismVertexAction
    (level : GaloisLevel diagram root) :
    Aut level.object →* Equiv.Perm level.semiGraph.Vertex where
  toFun := automorphismVertexPerm diagram root level
  map_one' := by
    apply Equiv.ext
    exact transition_vertex_id diagram root level
  map_mul' first second := by
    apply Equiv.ext
    intro vertex
    change finiteEtaleCoverVertexMap diagram (first * second).hom vertex =
      finiteEtaleCoverVertexMap diagram first.hom
        (finiteEtaleCoverVertexMap diagram second.hom vertex)
    rw [Aut.Aut_mul_def]
    exact finiteEtaleCoverVertexMap_comp diagram
      second.hom first.hom vertex

/-- An automorphism of the Galois object permutes the edges of its
associated finite-etale semigraph. -/
noncomputable def automorphismEdgePerm
    (level : GaloisLevel diagram root) (automorphism : Aut level.object) :
    Equiv.Perm level.semiGraph.Edge where
  toFun := finiteEtaleCoverEdgeMap diagram root automorphism.hom
  invFun := finiteEtaleCoverEdgeMap diagram root automorphism.inv
  left_inv edge := by
    rw [← finiteEtaleCoverEdgeMap_comp diagram root
      automorphism.hom automorphism.inv edge,
      automorphism.hom_inv_id]
    exact finiteEtaleCoverEdgeMap_id diagram root level.object edge
  right_inv edge := by
    rw [← finiteEtaleCoverEdgeMap_comp diagram root
      automorphism.inv automorphism.hom edge,
      automorphism.inv_hom_id]
    exact finiteEtaleCoverEdgeMap_id diagram root level.object edge

/-- The edge permutations form the finite-level deck action. -/
noncomputable def automorphismEdgeAction
    (level : GaloisLevel diagram root) :
    Aut level.object →* Equiv.Perm level.semiGraph.Edge where
  toFun := automorphismEdgePerm diagram root level
  map_one' := by
    apply Equiv.ext
    exact transition_edge_id diagram root level
  map_mul' first second := by
    apply Equiv.ext
    intro edge
    change finiteEtaleCoverEdgeMap diagram root (first * second).hom edge =
      finiteEtaleCoverEdgeMap diagram root first.hom
        (finiteEtaleCoverEdgeMap diagram root second.hom edge)
    rw [Aut.Aut_mul_def]
    exact finiteEtaleCoverEdgeMap_comp diagram root
      second.hom first.hom edge

/-- An automorphism of the Galois object permutes the total branches of its
associated finite-etale semigraph. -/
noncomputable def automorphismBranchPerm
    (level : GaloisLevel diagram root) (automorphism : Aut level.object) :
    Equiv.Perm level.semiGraph.TotalBranch where
  toFun := (finiteEtaleCoverTransition diagram root
    automorphism.hom).totalBranchMap
  invFun := (finiteEtaleCoverTransition diagram root
    automorphism.inv).totalBranchMap
  left_inv branch := by
    rcases branch with ⟨edge, branch⟩
    refine Sigma.ext ?_ ?_
    · change finiteEtaleCoverEdgeMap diagram root automorphism.inv
          (finiteEtaleCoverEdgeMap diagram root automorphism.hom edge) = edge
      rw [← finiteEtaleCoverEdgeMap_comp diagram root
        automorphism.hom automorphism.inv edge,
        automorphism.hom_inv_id]
      exact finiteEtaleCoverEdgeMap_id diagram root level.object edge
    · rfl
  right_inv branch := by
    rcases branch with ⟨edge, branch⟩
    refine Sigma.ext ?_ ?_
    · change finiteEtaleCoverEdgeMap diagram root automorphism.hom
          (finiteEtaleCoverEdgeMap diagram root automorphism.inv edge) = edge
      rw [← finiteEtaleCoverEdgeMap_comp diagram root
        automorphism.inv automorphism.hom edge,
        automorphism.inv_hom_id]
      exact finiteEtaleCoverEdgeMap_id diagram root level.object edge
    · rfl

/-- The total-branch permutations form the finite-level deck action. -/
noncomputable def automorphismBranchAction
    (level : GaloisLevel diagram root) :
    Aut level.object →* Equiv.Perm level.semiGraph.TotalBranch where
  toFun := automorphismBranchPerm diagram root level
  map_one' := by
    apply Equiv.ext
    rintro ⟨edge, branch⟩
    refine Sigma.ext (transition_edge_id diagram root level edge) ?_
    rfl
  map_mul' first second := by
    apply Equiv.ext
    rintro ⟨edge, branch⟩
    refine Sigma.ext ?_ ?_
    · change finiteEtaleCoverEdgeMap diagram root
          (first * second).hom edge =
        finiteEtaleCoverEdgeMap diagram root first.hom
          (finiteEtaleCoverEdgeMap diagram root second.hom edge)
      rw [Aut.Aut_mul_def]
      exact finiteEtaleCoverEdgeMap_comp diagram root
        second.hom first.hom edge
    · rfl

/-- The Galois automorphism group acts on the complete associated semigraph.
All three permutations are induced by the object automorphism, and incidence
compatibility follows from properness of the finite-etale transition. -/
noncomputable def automorphismAction
    (level : GaloisLevel diagram root) :
    level.semiGraph.Action (Aut level.object) where
  vertexAction := automorphismVertexAction diagram root level
  edgeAction := automorphismEdgeAction diagram root level
  branchAction := automorphismBranchAction diagram root level
  branch_edge := by
    intro automorphism branch
    rfl
  coincidence_action := by
    intro automorphism branch
    cases sourceCoincidence : level.semiGraph.coincidenceTotal branch with
    | none =>
        cases targetCoincidence : level.semiGraph.coincidenceTotal
            ((automorphismBranchAction diagram root level)
              automorphism branch) with
        | none => simp
        | some vertex =>
            have targetExists : ∃ targetVertex,
                level.semiGraph.coincidenceTotal
                  ((automorphismBranchAction diagram root level)
                    automorphism branch) = some targetVertex :=
              ⟨vertex, targetCoincidence⟩
            have sourceExists :=
              (finiteEtaleCoverTransition_isProper diagram root
                automorphism.hom branch.edge branch.2).mpr targetExists
            obtain ⟨sourceVertex, sourceEquality⟩ := sourceExists
            change level.semiGraph.coincidenceTotal branch =
              some sourceVertex at sourceEquality
            rw [sourceCoincidence] at sourceEquality
            cases sourceEquality
    | some vertex =>
        change level.semiGraph.coincidenceTotal
            ((finiteEtaleCoverTransition diagram root
              automorphism.hom).totalBranchMap branch) =
          some (finiteEtaleCoverVertexMap diagram
            automorphism.hom vertex)
        exact (finiteEtaleCoverTransition diagram root
          automorphism.hom).map_coincidence
            branch.edge branch.2 vertex sourceCoincidence

/-- The derived Galois action is transitive on every vertex fiber of the
finite-etale projection. -/
theorem vertexAction_transitive_on_projection_fiber
    (level : GaloisLevel diagram root)
    (first second : level.semiGraph.Vertex)
    (sameBase : level.projection.vertexMap first =
      level.projection.vertexMap second) :
    ∃ automorphism : Aut level.object,
      (automorphismAction diagram root level).vertexAction
        automorphism first = second := by
  rcases first with ⟨firstVertex, firstComponent⟩
  rcases second with ⟨secondVertex, secondComponent⟩
  change firstVertex = secondVertex at sameBase
  subst secondVertex
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (rootFiber diagram firstVertex) :=
    rootFiberFunctor diagram firstVertex
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  let firstPoint : (rootFiber diagram firstVertex).obj level.object :=
    firstComponent.out
  let secondPoint : (rootFiber diagram firstVertex).obj level.object :=
    secondComponent.out
  obtain ⟨automorphism, pointEquality⟩ :=
    MulAction.exists_smul_eq (Aut level.object) firstPoint secondPoint
  change (rootFiber diagram firstVertex).map automorphism.hom firstPoint =
    secondPoint at pointEquality
  refine ⟨automorphism, ?_⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change EtaleFundamentalGroup.fiberComponentHomMap
      (diagram.vertexAnabelioid firstVertex)
      (automorphism.hom.app firstVertex) firstComponent = secondComponent
  rw [← Quotient.out_eq' firstComponent,
    ← Quotient.out_eq' secondComponent]
  change Quotient.mk''
      ((rootFiber diagram firstVertex).map automorphism.hom firstPoint) =
    Quotient.mk'' secondPoint
  exact congrArg Quotient.mk'' pointEquality

/-- The derived Galois action is transitive on every edge fiber of the
finite-etale projection.  The chosen reference branch identifies the edge
fiber functor with the corresponding vertex fiber functor, so transitivity is
transported through that source-supplied fiber comparison. -/
theorem edgeAction_transitive_on_projection_fiber
    (level : GaloisLevel diagram root)
    (first second : level.semiGraph.Edge)
    (sameBase : level.projection.edgeMap first =
      level.projection.edgeMap second) :
    ∃ automorphism : Aut level.object,
      (automorphismAction diagram root level).edgeAction
        automorphism first = second := by
  rcases first with ⟨firstEdge, firstComponent⟩
  rcases second with ⟨secondEdge, secondComponent⟩
  change firstEdge = secondEdge at sameBase
  subst secondEdge
  let reference := coverReferenceBranch diagram root firstEdge
  let pointed := diagram.branchMorphism reference.branch reference.abuts
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid reference.vertex).fiberFunctor
  letI := (diagram.edgeAnabelioid firstEdge).coverCategory
  letI := (diagram.edgeAnabelioid firstEdge).galoisCategory
  letI := (diagram.edgeAnabelioid firstEdge).fiberFunctor
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (rootFiber diagram reference.vertex) :=
    rootFiberFunctor diagram reference.vertex
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  let firstPoint : (diagram.edgeAnabelioid firstEdge).fiber.obj
      (coverEdgeObject diagram root level.object firstEdge) :=
    firstComponent.out
  let secondPoint : (diagram.edgeAnabelioid firstEdge).fiber.obj
      (coverEdgeObject diagram root level.object firstEdge) :=
    secondComponent.out
  let firstVertexPoint :
      (rootFiber diagram reference.vertex).obj level.object :=
    pointed.fiberIso.hom.app (level.object.vertexObject reference.vertex)
      firstPoint
  let secondVertexPoint :
      (rootFiber diagram reference.vertex).obj level.object :=
    pointed.fiberIso.hom.app (level.object.vertexObject reference.vertex)
      secondPoint
  obtain ⟨automorphism, vertexPointEquality⟩ :=
    MulAction.exists_smul_eq
      (Aut level.object) firstVertexPoint secondVertexPoint
  change (rootFiber diagram reference.vertex).map automorphism.hom
      firstVertexPoint = secondVertexPoint at vertexPointEquality
  have edgePointEquality :
      (diagram.edgeAnabelioid firstEdge).fiber.map
          (reference.pullback.map
            (automorphism.hom.app reference.vertex)) firstPoint =
        secondPoint := by
    apply (ConcreteCategory.bijective_of_isIso
      (pointed.fiberIso.hom.app
        (level.object.vertexObject reference.vertex))).1
    have naturalityPoint :
        pointed.fiberIso.hom.app
              (level.object.vertexObject reference.vertex)
              ((diagram.edgeAnabelioid firstEdge).fiber.map
                (reference.pullback.map
                  (automorphism.hom.app reference.vertex)) firstPoint) =
            (rootFiber diagram reference.vertex).map automorphism.hom
              firstVertexPoint := by
      have hnatural := ConcreteCategory.congr_hom
        (pointed.fiberIso.hom.naturality
          (automorphism.hom.app reference.vertex)) firstPoint
      change
        pointed.fiberIso.hom.app
              (level.object.vertexObject reference.vertex)
              ((diagram.edgeAnabelioid firstEdge).fiber.map
                (reference.pullback.map
                  (automorphism.hom.app reference.vertex)) firstPoint) =
            (rootFiber diagram reference.vertex).map automorphism.hom
              firstVertexPoint at hnatural
      exact hnatural
    exact naturalityPoint.trans vertexPointEquality
  refine ⟨automorphism, ?_⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change EtaleFundamentalGroup.fiberComponentHomMap
      (diagram.edgeAnabelioid firstEdge)
      (reference.pullback.map
        (automorphism.hom.app reference.vertex)) firstComponent =
    secondComponent
  rw [← Quotient.out_eq' firstComponent,
    ← Quotient.out_eq' secondComponent]
  change Quotient.mk''
      ((diagram.edgeAnabelioid firstEdge).fiber.map
        (reference.pullback.map
          (automorphism.hom.app reference.vertex)) firstPoint) =
    Quotient.mk'' secondPoint
  exact congrArg Quotient.mk'' edgePointEquality

/-- Refinement of connected Galois objects descends automorphisms to the
coarser level.  Mathlib constructs this homomorphism from the unique
commuting automorphism, rather than accepting a transition homomorphism as
extra data. -/
noncomputable def automorphismTransition
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    Aut finer.object →* Aut coarser.object := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  exact PreGaloisCategory.autMapHom refinement.val

/-- Every coarser Galois symmetry lifts to a finer Galois symmetry. -/
theorem automorphismTransition_surjective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    Function.Surjective (automorphismTransition diagram root refinement) := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  exact PreGaloisCategory.autMap_surjective_of_isGalois refinement.val

/-- Refinement intertwines the derived Galois actions on vertices. -/
theorem transition_vertex_automorphism
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (automorphism : Aut finer.object) (vertex : finer.semiGraph.Vertex) :
    (transition diagram root refinement).vertexMap
        ((automorphismAction diagram root finer).vertexAction
          automorphism vertex) =
      (automorphismAction diagram root coarser).vertexAction
        (automorphismTransition diagram root refinement automorphism)
        ((transition diagram root refinement).vertexMap vertex) := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  change finiteEtaleCoverVertexMap diagram refinement.val
      (finiteEtaleCoverVertexMap diagram automorphism.hom vertex) =
    finiteEtaleCoverVertexMap diagram
      (PreGaloisCategory.autMap refinement.val automorphism).hom
      (finiteEtaleCoverVertexMap diagram refinement.val vertex)
  rw [← finiteEtaleCoverVertexMap_comp diagram
      automorphism.hom refinement.val vertex,
    ← finiteEtaleCoverVertexMap_comp diagram refinement.val
      (PreGaloisCategory.autMap refinement.val automorphism).hom vertex,
    PreGaloisCategory.comp_autMap]

/-- Refinement intertwines the derived Galois actions on edges. -/
theorem transition_edge_automorphism
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (automorphism : Aut finer.object) (edge : finer.semiGraph.Edge) :
    (transition diagram root refinement).edgeMap
        ((automorphismAction diagram root finer).edgeAction
          automorphism edge) =
      (automorphismAction diagram root coarser).edgeAction
        (automorphismTransition diagram root refinement automorphism)
        ((transition diagram root refinement).edgeMap edge) := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  change finiteEtaleCoverEdgeMap diagram root refinement.val
      (finiteEtaleCoverEdgeMap diagram root automorphism.hom edge) =
    finiteEtaleCoverEdgeMap diagram root
      (PreGaloisCategory.autMap refinement.val automorphism).hom
      (finiteEtaleCoverEdgeMap diagram root refinement.val edge)
  rw [← finiteEtaleCoverEdgeMap_comp diagram root
      automorphism.hom refinement.val edge,
    ← finiteEtaleCoverEdgeMap_comp diagram root refinement.val
      (PreGaloisCategory.autMap refinement.val automorphism).hom edge,
    PreGaloisCategory.comp_autMap]

/-- Refinement intertwines the derived Galois actions on total branches. -/
theorem transition_branch_automorphism
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (automorphism : Aut finer.object)
    (branch : finer.semiGraph.TotalBranch) :
    (transition diagram root refinement).totalBranchMap
        ((automorphismAction diagram root finer).branchAction
          automorphism branch) =
      (automorphismAction diagram root coarser).branchAction
        (automorphismTransition diagram root refinement automorphism)
        ((transition diagram root refinement).totalBranchMap branch) := by
  rcases branch with ⟨edge, branch⟩
  refine Sigma.ext
    (transition_edge_automorphism diagram root refinement automorphism edge) ?_
  rfl

/-- A finite base has finitely many lifted vertices at every Galois level. -/
noncomputable instance vertex_finite
    [Finite diagram.base.Vertex]
    (level : GaloisLevel diagram root) : Finite level.semiGraph.Vertex := by
  letI (vertex : diagram.base.Vertex) :
      Finite (CoverVertexComponent diagram level.object vertex) :=
    inferInstance
  change Finite (Σ vertex, CoverVertexComponent diagram level.object vertex)
  infer_instance

/-- A finite base has finitely many lifted edges at every Galois level. -/
noncomputable instance edge_finite
    [Finite diagram.base.Edge]
    (level : GaloisLevel diagram root) : Finite level.semiGraph.Edge := by
  letI (edge : diagram.base.Edge) :
      Finite (CoverEdgeComponent diagram root level.object edge) :=
    inferInstance
  change Finite (Σ edge, CoverEdgeComponent diagram root level.object edge)
  infer_instance

/-- A countable base has countably many lifted vertices at every Galois
level; every fiber over a base vertex is finite. -/
noncomputable instance vertex_countable
    [Countable diagram.base.Vertex]
    (level : GaloisLevel diagram root) : Countable level.semiGraph.Vertex := by
  letI (vertex : diagram.base.Vertex) :
      Countable (CoverVertexComponent diagram level.object vertex) :=
    Finite.to_countable
  change Countable
    (Σ vertex, CoverVertexComponent diagram level.object vertex)
  infer_instance

/-- A countable base has countably many lifted edges at every Galois level;
every fiber over a base edge is finite. -/
noncomputable instance edge_countable
    [Countable diagram.base.Edge]
    (level : GaloisLevel diagram root) : Countable level.semiGraph.Edge := by
  letI (edge : diagram.base.Edge) :
      Countable (CoverEdgeComponent diagram root level.object edge) :=
    Finite.to_countable
  change Countable
    (Σ edge, CoverEdgeComponent diagram root level.object edge)
  infer_instance

end GaloisLevel

end SourceSemiGraphOfAnabelioids.GluedObject

end Iut
