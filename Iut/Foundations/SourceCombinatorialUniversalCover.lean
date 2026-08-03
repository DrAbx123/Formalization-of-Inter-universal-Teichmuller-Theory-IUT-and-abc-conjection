/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Countable.Basic
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Tactic.DeriveCountable
import Iut.Foundations.SourceProfiniteSemiGraphSystem
import Iut.Foundations.SourceGluedGaloisLevelSystem
import Iut.Foundations.SourceGluedIsolatedGaloisLevelSystem

/-!
# Combinatorial universal covers of source semi-graphs

The universal cover used in *Semi-graphs of Anabelioids*, Definition 3.5 and
Proposition 3.6, is the tree of based reduced walks.  This file constructs that
tree before adding the finite-level deck action.  The walk remembers its
previous vertex in its type, so immediate reversal is excluded by construction
rather than removed by a quotient.
-/

namespace Iut

universe u

open CategoryTheory

namespace SourceCombinatorialUniversalCover

/-- Vertices of the faithful barycentric incidence realization of a source
semi-graph.  A separate node for every total branch prevents the simple-graph
realization from collapsing loops or parallel incidences. -/
inductive IncidenceNode (semiGraph : SourceSemiGraph.{u})
  | vertex (point : semiGraph.CompactVertex)
  | edge (edge : semiGraph.Edge)
  | branch (branch : semiGraph.TotalBranch)

namespace IncidenceNode

variable (semiGraph : SourceSemiGraph.{u})

/-- The faithful incidence-node type is canonically the disjoint union of its
three kinds of nodes. -/
def incidenceNodeEquiv :
    (semiGraph.CompactVertex ⊕ semiGraph.Edge ⊕ semiGraph.TotalBranch) ≃
      IncidenceNode semiGraph where
  toFun
    | Sum.inl vertexValue => IncidenceNode.vertex vertexValue
    | Sum.inr (Sum.inl edgeValue) => IncidenceNode.edge edgeValue
    | Sum.inr (Sum.inr branchValue) => IncidenceNode.branch branchValue
  invFun
    | IncidenceNode.vertex vertexValue => Sum.inl vertexValue
    | IncidenceNode.edge edgeValue => Sum.inr (Sum.inl edgeValue)
    | IncidenceNode.branch branchValue => Sum.inr (Sum.inr branchValue)
  left_inv value := by cases value with
    | inl _ => rfl
    | inr value => cases value <;> rfl
  right_inv value := by cases value <;> rfl

noncomputable instance [Countable semiGraph.Vertex]
    [Countable semiGraph.Edge] : Countable (IncidenceNode semiGraph) := by
  letI (edge : semiGraph.Edge) : Countable (semiGraph.Branch edge) :=
    Finite.to_countable
  letI : Countable semiGraph.TotalBranch := by
    change Countable (Σ edge, semiGraph.Branch edge)
    infer_instance
  letI : Countable semiGraph.NonVerticialBranch := by
    change Countable {branch : semiGraph.TotalBranch //
      semiGraph.coincidenceTotal branch = none}
    infer_instance
  letI : Countable semiGraph.CompactVertex := by
    change Countable (semiGraph.Vertex ⊕ semiGraph.NonVerticialBranch)
    infer_instance
  exact Countable.of_equiv _ (incidenceNodeEquiv semiGraph)

noncomputable instance [Finite semiGraph.Vertex]
    [Finite semiGraph.Edge] : Finite (IncidenceNode semiGraph) := by
  letI (edge : semiGraph.Edge) : Fintype (semiGraph.Branch edge) :=
    semiGraph.branchFintype edge
  letI : Finite semiGraph.TotalBranch := by
    change Finite (Σ edge, semiGraph.Branch edge)
    infer_instance
  letI : Finite semiGraph.NonVerticialBranch := by
    change Finite {branch : semiGraph.TotalBranch //
      semiGraph.coincidenceTotal branch = none}
    infer_instance
  letI : Fintype semiGraph.Vertex := Fintype.ofFinite _
  letI : Fintype semiGraph.Edge := Fintype.ofFinite _
  letI : Fintype semiGraph.TotalBranch := Fintype.ofFinite _
  letI : Fintype semiGraph.NonVerticialBranch := Fintype.ofFinite _
  letI : Fintype semiGraph.CompactVertex := by
    change Fintype (semiGraph.Vertex ⊕ semiGraph.NonVerticialBranch)
    infer_instance
  letI : Fintype
      (semiGraph.CompactVertex ⊕ semiGraph.Edge ⊕ semiGraph.TotalBranch) :=
    inferInstance
  letI : Fintype (IncidenceNode semiGraph) :=
    Fintype.ofEquiv _ (incidenceNodeEquiv semiGraph)
  infer_instance

/-- One directed half of the barycentric incidence relation.  `fromRel`
symmetrizes it below. -/
def incidenceRel : IncidenceNode semiGraph → IncidenceNode semiGraph → Prop
  | IncidenceNode.edge edgeValue, IncidenceNode.branch branchValue =>
      branchValue.edge = edgeValue
  | IncidenceNode.branch branchValue, IncidenceNode.vertex vertexValue =>
      semiGraph.compactification.coincidence branchValue.1 branchValue.2 =
        some vertexValue
  | _, _ => False

/-- The faithful incidence graph of the compactified source semi-graph. -/
def incidenceGraph : SimpleGraph (IncidenceNode semiGraph) :=
  SimpleGraph.fromRel (incidenceRel semiGraph)

theorem incidenceRel_ne {first second : IncidenceNode semiGraph}
    (related : incidenceRel semiGraph first second) : first ≠ second := by
  cases first <;> cases second <;> simp [incidenceRel] at related ⊢

/-- A semi-graph morphism induces a map of faithful incidence nodes through
its canonical compactification map. -/
noncomputable def map {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) :
    IncidenceNode semiGraph → IncidenceNode target :=
  fun point => incidenceNodeEquiv target <|
    Sum.map hom.compactVertexMap
      (Sum.map hom.edgeMap hom.totalBranchMap)
      ((incidenceNodeEquiv semiGraph).symm point)

@[simp]
theorem map_vertex {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (vertex : semiGraph.CompactVertex) :
    map semiGraph hom (IncidenceNode.vertex vertex) =
      IncidenceNode.vertex (hom.compactVertexMap vertex) :=
  rfl

@[simp]
theorem map_edge {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (edge : semiGraph.Edge) :
    map semiGraph hom (IncidenceNode.edge edge) =
      IncidenceNode.edge (hom.edgeMap edge) :=
  rfl

@[simp]
theorem map_branch {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (branch : semiGraph.TotalBranch) :
    map semiGraph hom (IncidenceNode.branch branch) =
      IncidenceNode.branch (hom.totalBranchMap branch) :=
  rfl

theorem incidenceRel_map {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) {first second : IncidenceNode semiGraph}
    (related : incidenceRel semiGraph first second) :
    incidenceRel target (map semiGraph hom first) (map semiGraph hom second) := by
  cases first <;> cases second <;>
    simp only [incidenceRel, map_vertex, map_edge, map_branch] at related ⊢
  case edge.branch edge branch =>
    rcases branch with ⟨branchEdge, branch⟩
    exact congrArg hom.edgeMap related
  case branch.vertex branch vertex =>
    exact hom.compactificationMap.map_coincidence
      branch.1 branch.2 vertex related

/-- The induced faithful-incidence map is a simple-graph homomorphism. -/
noncomputable def incidenceGraphHom {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) :
    incidenceGraph semiGraph →g incidenceGraph target where
  toFun := map semiGraph hom
  map_rel' := by
    intro first second adjacent
    rw [incidenceGraph, SimpleGraph.fromRel_adj] at adjacent ⊢
    rcases adjacent.2 with related | related
    · let mapped := incidenceRel_map semiGraph hom related
      exact ⟨incidenceRel_ne target mapped, Or.inl mapped⟩
    · let mapped := incidenceRel_map semiGraph hom related
      exact ⟨(incidenceRel_ne target mapped).symm, Or.inr mapped⟩

/-- A proper semi-graph morphism sends a nonverticial branch to a
nonverticial branch. -/
noncomputable def nonVerticialMap {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper) :
    semiGraph.NonVerticialBranch → target.NonVerticialBranch :=
  fun branch => ⟨hom.totalBranchMap branch.1, by
    change target.coincidence (hom.edgeMap branch.1.1)
      (hom.branchEquiv branch.1.1 branch.1.2) = none
    cases targetCoincidence : target.coincidence (hom.edgeMap branch.1.1)
        (hom.branchEquiv branch.1.1 branch.1.2) with
    | none => rfl
    | some vertex =>
        obtain ⟨sourceVertex, sourceCoincidence⟩ :=
          (proper branch.1.1 branch.1.2).mpr ⟨vertex, targetCoincidence⟩
        have sourceNone := branch.2
        change semiGraph.coincidence branch.1.1 branch.1.2 = none at sourceNone
        rw [sourceCoincidence] at sourceNone
        cases sourceNone⟩

/-- For a proper morphism the incidence-node map has a branchwise form with
no runtime case split in the compactified vertex component. -/
noncomputable def properMap {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper) :
    IncidenceNode semiGraph → IncidenceNode target :=
  fun point => incidenceNodeEquiv target <|
    Sum.map (Sum.map hom.vertexMap (nonVerticialMap semiGraph hom proper))
      (Sum.map hom.edgeMap hom.totalBranchMap)
      ((incidenceNodeEquiv semiGraph).symm point)

@[simp]
theorem properMap_vertex_original {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper)
    (vertex : semiGraph.Vertex) :
    properMap semiGraph hom proper (IncidenceNode.vertex (Sum.inl vertex)) =
      IncidenceNode.vertex (Sum.inl (hom.vertexMap vertex)) :=
  rfl

@[simp]
theorem properMap_vertex_boundary {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper)
    (branch : semiGraph.NonVerticialBranch) :
    properMap semiGraph hom proper (IncidenceNode.vertex (Sum.inr branch)) =
      IncidenceNode.vertex
        (Sum.inr (nonVerticialMap semiGraph hom proper branch)) :=
  rfl

@[simp]
theorem properMap_edge {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper)
    (edge : semiGraph.Edge) :
    properMap semiGraph hom proper (IncidenceNode.edge edge) =
      IncidenceNode.edge (hom.edgeMap edge) :=
  rfl

@[simp]
theorem properMap_branch {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper)
    (branch : semiGraph.TotalBranch) :
    properMap semiGraph hom proper (IncidenceNode.branch branch) =
      IncidenceNode.branch (hom.totalBranchMap branch) :=
  rfl

theorem properMap_eq_map {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper)
    (point : IncidenceNode semiGraph) :
    properMap semiGraph hom proper point = map semiGraph hom point := by
  cases point with
  | vertex vertex =>
      cases vertex with
      | inl vertex => rfl
      | inr branch =>
          rw [properMap_vertex_boundary, map_vertex]
          rw [hom.compactVertexMap_boundary_of_none _
            (nonVerticialMap semiGraph hom proper branch).2]
          congr 2
  | edge edge => rfl
  | branch branch => rfl

/-- The branchwise incidence-node map of a composite proper morphism is the
composite of the two branchwise incidence-node maps. -/
theorem properMap_comp
    {middle target : SourceSemiGraph.{u}}
    (first : semiGraph.Hom middle) (second : middle.Hom target)
    (firstProper : first.IsProper) (secondProper : second.IsProper)
    (point : IncidenceNode semiGraph) :
    properMap semiGraph (first.comp second)
        (firstProper.comp secondProper) point =
      properMap middle second secondProper
        (properMap semiGraph first firstProper point) := by
  cases point with
  | vertex point =>
      cases point with
      | inl vertex => rfl
      | inr branch =>
          simp only [properMap_vertex_boundary]
          apply congrArg (fun value => IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          rfl
  | edge edge => rfl
  | branch branch => rfl

/-- Faithful-incidence graph homomorphism in the branchwise form available
for proper semi-graph morphisms. -/
noncomputable def properIncidenceGraphHom {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper) :
    incidenceGraph semiGraph →g incidenceGraph target where
  toFun := properMap semiGraph hom proper
  map_rel' := by
    intro first second adjacent
    rw [properMap_eq_map, properMap_eq_map]
    exact (incidenceGraphHom semiGraph hom).map_rel adjacent

@[simp]
theorem properIncidenceGraphHom_apply {target : SourceSemiGraph.{u}}
    (hom : semiGraph.Hom target) (proper : hom.IsProper)
    (point : IncidenceNode semiGraph) :
    properIncidenceGraphHom semiGraph hom proper point =
      properMap semiGraph hom proper point :=
  rfl

@[simp]
theorem edge_branch_adj (edge : semiGraph.Edge)
    (branch : semiGraph.TotalBranch) :
    (incidenceGraph semiGraph).Adj (IncidenceNode.edge edge)
      (IncidenceNode.branch branch) ↔
      branch.edge = edge := by
  simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]

@[simp]
theorem branch_edge_adj (branch : semiGraph.TotalBranch)
    (edge : semiGraph.Edge) :
    (incidenceGraph semiGraph).Adj (IncidenceNode.branch branch)
      (IncidenceNode.edge edge) ↔
      branch.edge = edge := by
  rw [SimpleGraph.adj_comm, edge_branch_adj]

@[simp]
theorem branch_vertex_adj (branch : semiGraph.TotalBranch)
    (vertex : semiGraph.CompactVertex) :
    (incidenceGraph semiGraph).Adj (IncidenceNode.branch branch)
      (IncidenceNode.vertex vertex) ↔
      semiGraph.compactification.coincidence branch.1 branch.2 =
        some vertex := by
  simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]

@[simp]
theorem vertex_branch_adj (vertex : semiGraph.CompactVertex)
    (branch : semiGraph.TotalBranch) :
    (incidenceGraph semiGraph).Adj (IncidenceNode.vertex vertex)
      (IncidenceNode.branch branch) ↔
      semiGraph.compactification.coincidence branch.1 branch.2 =
        some vertex := by
  rw [SimpleGraph.adj_comm, branch_vertex_adj]

private theorem coincidence_eq_of_compactification_original
    (branch : semiGraph.TotalBranch) (vertex : semiGraph.Vertex)
    (coincidence : semiGraph.compactification.coincidenceTotal branch =
      some (Sum.inl vertex)) :
    semiGraph.coincidenceTotal branch = some vertex := by
  rcases branch with ⟨edge, branch⟩
  change semiGraph.compactification.coincidence edge branch =
    some (Sum.inl vertex) at coincidence
  change semiGraph.coincidence edge branch = some vertex
  cases sourceCoincidence : semiGraph.coincidence edge branch with
  | none =>
      rw [semiGraph.compactification_coincidence_of_none sourceCoincidence]
        at coincidence
      cases coincidence
  | some sourceVertex =>
      rw [semiGraph.compactification_coincidence_of_some sourceCoincidence]
        at coincidence
      have vertexEquality : sourceVertex = vertex := by
        exact Sum.inl.inj (Option.some.inj coincidence)
      subst sourceVertex
      rfl

private theorem totalBranch_eq_of_compactification_boundary
    (branch : semiGraph.TotalBranch)
    (boundary : semiGraph.NonVerticialBranch)
    (coincidence : semiGraph.compactification.coincidenceTotal branch =
      some (Sum.inr boundary)) : branch = boundary.1 := by
  rcases branch with ⟨edge, branch⟩
  change semiGraph.compactification.coincidence edge branch =
    some (Sum.inr boundary) at coincidence
  cases sourceCoincidence : semiGraph.coincidence edge branch with
  | some sourceVertex =>
      rw [semiGraph.compactification_coincidence_of_some sourceCoincidence]
        at coincidence
      cases coincidence
  | none =>
      rw [semiGraph.compactification_coincidence_of_none sourceCoincidence]
        at coincidence
      exact congrArg Subtype.val <| Sum.inr.inj <| Option.some.inj coincidence

/-! ## Compressing faithful-incidence walks back to semi-graph paths -/

/-- Reachability among genuine semi-graph vertices, with closed-edge
adjacency as in the source definition of connectedness. -/
abbrev VertexReachableFrom (start : semiGraph.Vertex) (target : semiGraph.Vertex) :=
  Relation.ReflTransGen semiGraph.Adjacent start target

/-- The state retained while an incidence walk is between genuine vertices.
At an edge, branch, or compactification-boundary node it remembers a genuine
vertex already reached and incident to the supporting edge. -/
def IncidenceReachableState (start : semiGraph.Vertex) :
    IncidenceNode semiGraph → Prop
  | .vertex (.inl targetVertex) =>
      VertexReachableFrom semiGraph start targetVertex
  | .vertex (.inr boundary) =>
      ∃ reachedVertex, VertexReachableFrom semiGraph start reachedVertex ∧
        semiGraph.EdgeAbuts boundary.1.1 reachedVertex
  | .edge targetEdge =>
      ∃ reachedVertex, VertexReachableFrom semiGraph start reachedVertex ∧
        semiGraph.EdgeAbuts targetEdge reachedVertex
  | .branch targetBranch =>
      ∃ reachedVertex, VertexReachableFrom semiGraph start reachedVertex ∧
        semiGraph.EdgeAbuts targetBranch.1 reachedVertex

/-- If a reached vertex and a displayed branch both abut one edge, then the
branch endpoint is reachable: either both incidences are the same, or the
two distinct branches exhibit one closed-edge adjacency. -/
theorem vertexReachable_of_edgeAbuts_branchAbuts
    (start reached target : semiGraph.Vertex) (edge : semiGraph.Edge)
    (branch : semiGraph.Branch edge)
    (reachable : VertexReachableFrom semiGraph start reached)
    (edgeAbuts : semiGraph.EdgeAbuts edge reached)
    (branchAbuts : semiGraph.BranchAbuts branch target) :
    VertexReachableFrom semiGraph start target := by
  obtain ⟨reachedBranch, reachedBranchAbuts⟩ := edgeAbuts
  by_cases sameBranch : reachedBranch = branch
  · subst reachedBranch
    have vertexEquality : reached = target :=
      Option.some.inj (reachedBranchAbuts.symm.trans branchAbuts)
    subst target
    exact reachable
  · exact reachable.tail ⟨edge, reachedBranch, branch, sameBranch,
      reachedBranchAbuts, branchAbuts⟩

/-- One faithful-incidence step preserves the compressed reachability state. -/
theorem incidenceReachableState_step
    (start : semiGraph.Vertex) {first second : IncidenceNode semiGraph}
    (adjacent : (incidenceGraph semiGraph).Adj first second)
    (state : IncidenceReachableState semiGraph start first) :
    IncidenceReachableState semiGraph start second := by
  cases first with
  | vertex firstVertex =>
      cases second with
      | vertex secondVertex =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at adjacent
      | edge secondEdge =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at adjacent
      | branch secondBranch =>
          have branchEndpoint :=
            (vertex_branch_adj semiGraph firstVertex secondBranch).mp adjacent
          cases firstVertex with
          | inl firstVertex =>
              exact ⟨firstVertex, state,
                ⟨secondBranch.2,
                  coincidence_eq_of_compactification_original
                    semiGraph secondBranch firstVertex branchEndpoint⟩⟩
          | inr boundary =>
              have branchEquality :=
                totalBranch_eq_of_compactification_boundary
                  semiGraph secondBranch boundary branchEndpoint
              rcases state with ⟨vertex, reachable, edgeAbuts⟩
              refine ⟨vertex, reachable, ?_⟩
              simpa only [branchEquality] using edgeAbuts
  | edge firstEdge =>
      cases second with
      | vertex secondVertex =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at adjacent
      | edge secondEdge =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at adjacent
      | branch secondBranch =>
          have support :=
            (edge_branch_adj semiGraph firstEdge secondBranch).mp adjacent
          rcases state with ⟨vertex, reachable, edgeAbuts⟩
          subst firstEdge
          exact ⟨vertex, reachable, edgeAbuts⟩
  | branch firstBranch =>
      cases second with
      | edge secondEdge =>
          have support :=
            (branch_edge_adj semiGraph firstBranch secondEdge).mp adjacent
          rcases state with ⟨vertex, reachable, edgeAbuts⟩
          subst secondEdge
          exact ⟨vertex, reachable, edgeAbuts⟩
      | branch secondBranch =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at adjacent
      | vertex secondVertex =>
          have branchEndpoint :=
            (branch_vertex_adj semiGraph firstBranch secondVertex).mp adjacent
          rcases state with ⟨vertex, reachable, edgeAbuts⟩
          cases secondVertex with
          | inl secondVertex =>
              exact vertexReachable_of_edgeAbuts_branchAbuts semiGraph
                start vertex secondVertex firstBranch.1 firstBranch.2
                reachable edgeAbuts
                (coincidence_eq_of_compactification_original
                  semiGraph firstBranch secondVertex branchEndpoint)
          | inr boundary =>
              refine ⟨vertex, reachable, ?_⟩
              have branchEquality :=
                totalBranch_eq_of_compactification_boundary
                  semiGraph firstBranch boundary branchEndpoint
              simpa only [← branchEquality] using edgeAbuts

/-- A faithful-incidence walk transports the compressed reachability state
from its first node to its last node. -/
theorem incidenceReachableState_walk
    (start : semiGraph.Vertex) {first second : IncidenceNode semiGraph}
    (walk : (incidenceGraph semiGraph).Walk first second)
    (state : IncidenceReachableState semiGraph start first) :
    IncidenceReachableState semiGraph start second := by
  induction walk with
  | nil => exact state
  | @cons first next last adjacent tail inductionHypothesis =>
      exact inductionHypothesis <|
        incidenceReachableState_step semiGraph start adjacent state

/-- A walk in the faithful incidence graph between genuine vertex nodes
compresses to a path in the original semi-graph. -/
theorem vertexReachable_of_incidenceWalk
    (start target : semiGraph.Vertex)
    (walk : (incidenceGraph semiGraph).Walk
      (IncidenceNode.vertex (Sum.inl start))
      (IncidenceNode.vertex (Sum.inl target))) :
    VertexReachableFrom semiGraph start target := by
  have initial : IncidenceReachableState semiGraph start
      (IncidenceNode.vertex (Sum.inl start)) := by
    exact Relation.ReflTransGen.refl
  exact incidenceReachableState_walk semiGraph start walk initial

/-- Connectedness of the faithful incidence graph implies connectedness of
the underlying semi-graph whenever a genuine vertex exists. -/
theorem isConnected_of_incidenceGraph_connected
    [Nonempty semiGraph.Vertex]
    (connected : (incidenceGraph semiGraph).Connected) :
    semiGraph.IsConnected := by
  refine Or.inl ⟨inferInstance, ?_, ?_⟩
  · intro edge
    obtain ⟨root⟩ := (inferInstance : Nonempty semiGraph.Vertex)
    let edgeNode := IncidenceNode.edge edge
    obtain ⟨walk⟩ := connected
      (IncidenceNode.vertex (Sum.inl root)) edgeNode
    have state : IncidenceReachableState semiGraph root edgeNode := by
      have initial : IncidenceReachableState semiGraph root
          (IncidenceNode.vertex (Sum.inl root)) := by
        exact Relation.ReflTransGen.refl
      exact incidenceReachableState_walk semiGraph root walk initial
    rcases state with ⟨vertex, _, edgeAbuts⟩
    exact ⟨vertex, edgeAbuts⟩
  · intro first second
    obtain ⟨walk⟩ := connected
      (IncidenceNode.vertex (Sum.inl first))
      (IncidenceNode.vertex (Sum.inl second))
    exact vertexReachable_of_incidenceWalk semiGraph first second walk

/-- Distinct branches remain distinct vertices of the incidence graph. -/
theorem branch_injective :
    Function.Injective (IncidenceNode.branch :
      semiGraph.TotalBranch → IncidenceNode semiGraph) := by
  intro first second equality
  exact IncidenceNode.branch.inj equality

/-- Hence the two branch labels of an edge remain distinct even for a loop. -/
theorem branches_distinct {edge : semiGraph.Edge}
    {first second : semiGraph.Branch edge} (different : first ≠ second) :
    IncidenceNode.branch (⟨edge, first⟩ : semiGraph.TotalBranch) ≠
      IncidenceNode.branch ⟨edge, second⟩ := by
  exact fun equality => different <| Sigma.mk.inj_iff.mp
    (branch_injective semiGraph equality) |>.2 |> eq_of_heq

variable {Acting : Type u} [Group Acting]

/-- The action induced on nonverticial branches. -/
def nonVerticialBranchPerm (action : semiGraph.Action Acting) (g : Acting) :
    Equiv.Perm semiGraph.NonVerticialBranch where
  toFun branch := ⟨action.branchAction g branch.1, by
    rw [action.coincidence_action, branch.2]
    rfl⟩
  invFun branch := ⟨action.branchAction g⁻¹ branch.1, by
    rw [action.coincidence_action, branch.2]
    rfl⟩
  left_inv branch := by
    apply Subtype.ext
    simp [map_inv]
  right_inv branch := by
    apply Subtype.ext
    simp [map_inv]

@[simp]
theorem nonVerticialBranchPerm_one (action : semiGraph.Action Acting) :
    nonVerticialBranchPerm semiGraph action 1 = 1 := by
  apply Equiv.ext
  intro branch
  apply Subtype.ext
  simp [nonVerticialBranchPerm]

@[simp]
theorem nonVerticialBranchPerm_mul (action : semiGraph.Action Acting)
    (first second : Acting) :
    nonVerticialBranchPerm semiGraph action (first * second) =
      nonVerticialBranchPerm semiGraph action first *
        nonVerticialBranchPerm semiGraph action second := by
  apply Equiv.ext
  intro branch
  apply Subtype.ext
  simp [nonVerticialBranchPerm, map_mul]

/-- The action induced on compactified vertices. -/
def compactVertexPerm (action : semiGraph.Action Acting) (g : Acting) :
    Equiv.Perm semiGraph.CompactVertex :=
  Equiv.sumCongr (action.vertexAction g)
    (nonVerticialBranchPerm semiGraph action g)

@[simp]
theorem compactVertexPerm_one (action : semiGraph.Action Acting) :
    compactVertexPerm semiGraph action 1 = 1 := by
  apply Equiv.ext
  intro vertex
  cases vertex with
  | inl vertex =>
      simp only [compactVertexPerm]
      rw [map_one]
      rfl
  | inr branch =>
      simp only [compactVertexPerm]
      rw [nonVerticialBranchPerm_one]
      rfl

@[simp]
theorem compactVertexPerm_mul (action : semiGraph.Action Acting)
    (first second : Acting) :
    compactVertexPerm semiGraph action (first * second) =
      compactVertexPerm semiGraph action first *
        compactVertexPerm semiGraph action second := by
  apply Equiv.ext
  intro vertex
  cases vertex with
  | inl vertex =>
      simp only [compactVertexPerm, Equiv.Perm.mul_apply]
      rw [map_mul]
      rfl
  | inr branch =>
      simp only [compactVertexPerm, Equiv.Perm.mul_apply]
      rw [nonVerticialBranchPerm_mul]
      rfl

/-- Compactification coincidence is equivariant for the induced action. -/
theorem compactificationCoincidence_action
    (action : semiGraph.Action Acting) (g : Acting)
    (branch : semiGraph.TotalBranch) :
    semiGraph.compactification.coincidenceTotal
        (action.branchAction g branch) =
      (semiGraph.compactification.coincidenceTotal branch).map
        (compactVertexPerm semiGraph action g) := by
  cases sourceCoincidence : semiGraph.coincidenceTotal branch with
  | some vertex =>
      have targetCoincidence := action.coincidence_action g branch
      rw [sourceCoincidence] at targetCoincidence
      change semiGraph.coincidenceTotal (action.branchAction g branch) =
        some (action.vertexAction g vertex) at targetCoincidence
      change semiGraph.compactification.coincidence
          (action.branchAction g branch).1
          (action.branchAction g branch).2 = _
      rw [semiGraph.compactification_coincidence_of_some targetCoincidence]
      change some (Sum.inl (action.vertexAction g vertex)) = _
      rw [show semiGraph.compactification.coincidenceTotal branch =
          some (Sum.inl vertex) by
        exact semiGraph.compactification_coincidence_of_some sourceCoincidence]
      rfl
  | none =>
      have targetCoincidence := action.coincidence_action g branch
      rw [sourceCoincidence] at targetCoincidence
      change semiGraph.coincidenceTotal (action.branchAction g branch) = none
        at targetCoincidence
      change semiGraph.compactification.coincidence
          (action.branchAction g branch).1
          (action.branchAction g branch).2 = _
      rw [semiGraph.compactification_coincidence_of_none targetCoincidence]
      change some (Sum.inr _) = _
      rw [show semiGraph.compactification.coincidenceTotal branch =
          some (Sum.inr ⟨branch, sourceCoincidence⟩) by
        exact semiGraph.compactification_coincidence_of_none sourceCoincidence]
      rfl

/-- The product permutation on the three kinds of incidence nodes. -/
def incidenceSumPerm (action : semiGraph.Action Acting) (g : Acting) :
    Equiv.Perm
      (semiGraph.CompactVertex ⊕ semiGraph.Edge ⊕ semiGraph.TotalBranch) :=
  Equiv.sumCongr (compactVertexPerm semiGraph action g)
    (Equiv.sumCongr (action.edgeAction g) (action.branchAction g))

@[simp]
theorem incidenceSumPerm_one (action : semiGraph.Action Acting) :
    incidenceSumPerm semiGraph action 1 = 1 := by
  apply Equiv.ext
  intro point
  cases point with
  | inl vertex =>
      simp only [incidenceSumPerm, Equiv.sumCongr_apply, Sum.map_inl]
      rw [compactVertexPerm_one]
      rfl
  | inr point =>
      cases point with
      | inl edge =>
          simp only [incidenceSumPerm, Equiv.sumCongr_apply, Sum.map_inr,
            Sum.map_inl]
          rw [map_one]
          rfl
      | inr branch =>
          simp only [incidenceSumPerm, Equiv.sumCongr_apply, Sum.map_inr]
          rw [map_one]
          rfl

@[simp]
theorem incidenceSumPerm_mul (action : semiGraph.Action Acting)
    (first second : Acting) :
    incidenceSumPerm semiGraph action (first * second) =
      incidenceSumPerm semiGraph action first *
        incidenceSumPerm semiGraph action second := by
  apply Equiv.ext
  intro point
  cases point with
  | inl vertex =>
      simp only [incidenceSumPerm, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.Perm.mul_apply]
      rw [compactVertexPerm_mul]
      rfl
  | inr point =>
      cases point with
      | inl edge =>
          simp only [incidenceSumPerm, Equiv.sumCongr_apply, Sum.map_inr,
            Sum.map_inl, Equiv.Perm.mul_apply]
          rw [map_mul]
          rfl
      | inr branch =>
          simp only [incidenceSumPerm, Equiv.sumCongr_apply, Sum.map_inr,
            Equiv.Perm.mul_apply]
          rw [map_mul]
          rfl

/-- The induced permutation of faithful incidence nodes. -/
def incidencePerm (action : semiGraph.Action Acting) (g : Acting) :
    Equiv.Perm (IncidenceNode semiGraph) :=
  (incidenceNodeEquiv semiGraph).symm |>.trans
    ((incidenceSumPerm semiGraph action g).trans (incidenceNodeEquiv semiGraph))

@[simp]
theorem incidencePerm_vertex (action : semiGraph.Action Acting) (g : Acting)
    (vertex : semiGraph.CompactVertex) :
    incidencePerm semiGraph action g (IncidenceNode.vertex vertex) =
      IncidenceNode.vertex (compactVertexPerm semiGraph action g vertex) :=
  rfl

@[simp]
theorem incidencePerm_edge (action : semiGraph.Action Acting) (g : Acting)
    (edge : semiGraph.Edge) :
    incidencePerm semiGraph action g (IncidenceNode.edge edge) =
      IncidenceNode.edge (action.edgeAction g edge) :=
  rfl

@[simp]
theorem incidencePerm_branch (action : semiGraph.Action Acting) (g : Acting)
    (branch : semiGraph.TotalBranch) :
    incidencePerm semiGraph action g (IncidenceNode.branch branch) =
      IncidenceNode.branch (action.branchAction g branch) :=
  rfl

@[simp]
theorem incidencePerm_one (action : semiGraph.Action Acting) :
    incidencePerm semiGraph action 1 = 1 := by
  apply Equiv.ext
  intro point
  change (incidenceNodeEquiv semiGraph)
      (incidenceSumPerm semiGraph action 1
        ((incidenceNodeEquiv semiGraph).symm point)) = point
  rw [incidenceSumPerm_one]
  exact (incidenceNodeEquiv semiGraph).apply_symm_apply point

@[simp]
theorem incidencePerm_mul (action : semiGraph.Action Acting)
    (first second : Acting) :
    incidencePerm semiGraph action (first * second) =
      incidencePerm semiGraph action first *
        incidencePerm semiGraph action second := by
  apply Equiv.ext
  intro point
  rw [Equiv.Perm.mul_apply]
  simp only [incidencePerm, Equiv.trans_apply]
  rw [incidenceSumPerm_mul]
  rw [Equiv.Perm.mul_apply]
  rw [(incidenceNodeEquiv semiGraph).symm_apply_apply]

/-- The directed incidence relation is invariant under the induced action. -/
theorem incidenceRel_action_iff (action : semiGraph.Action Acting) (g : Acting)
    (first second : IncidenceNode semiGraph) :
    incidenceRel semiGraph (incidencePerm semiGraph action g first)
        (incidencePerm semiGraph action g second) ↔
      incidenceRel semiGraph first second := by
  cases first <;> cases second <;>
    simp only [incidencePerm_vertex, incidencePerm_edge,
      incidencePerm_branch, incidenceRel]
  case edge.branch edge branch =>
    rw [action.branch_edge]
    exact (action.edgeAction g).injective.eq_iff
  case branch.vertex branch vertex =>
    have equivariance := compactificationCoincidence_action
      semiGraph action g branch
    change semiGraph.compactification.coincidenceTotal
        (action.branchAction g branch) =
          some (compactVertexPerm semiGraph action g vertex) ↔
      semiGraph.compactification.coincidenceTotal branch = some vertex
    rw [equivariance]
    change Option.map (compactVertexPerm semiGraph action g)
        (semiGraph.compactification.coincidenceTotal branch) =
          Option.map (compactVertexPerm semiGraph action g) (some vertex) ↔
      semiGraph.compactification.coincidenceTotal branch = some vertex
    exact (Option.map_injective
      (compactVertexPerm semiGraph action g).injective).eq_iff

/-- Every source semi-graph action acts by automorphisms of its faithful
incidence graph. -/
def incidenceIso (action : semiGraph.Action Acting) (g : Acting) :
    incidenceGraph semiGraph ≃g incidenceGraph semiGraph where
  toEquiv := incidencePerm semiGraph action g
  map_rel_iff' := by
    intro first second
    rw [incidenceGraph, SimpleGraph.fromRel_adj,
      incidenceRel_action_iff, incidenceRel_action_iff]
    simp

end IncidenceNode

variable {Vertex : Type u} (graph : SimpleGraph Vertex) (root : Vertex)

/-- A based walk with no immediate reversal.  The first index is the previous
vertex, when one exists, and the second index is the current endpoint. -/
inductive ReducedWalk : Option Vertex → Vertex → Type u
  | nil : ReducedWalk none root
  | step {previous current next}
      (walk : ReducedWalk previous current)
      (adjacent : graph.Adj current next)
      (notBacktrack : previous ≠ some next) :
      ReducedWalk (some current) next
  deriving Countable

namespace ReducedWalk

/-- Number of edges in a reduced walk. -/
def length : {previous : Option Vertex} → {current : Vertex} →
    ReducedWalk graph root previous current → ℕ
  | _, _, .nil => 0
  | _, _, .step walk _ _ => walk.length + 1

/-- Vertices visited by a reduced walk, in reverse order from endpoint to
root. -/
def vertices : {previous : Option Vertex} → {current : Vertex} →
    ReducedWalk graph root previous current → List Vertex
  | _, _, .nil => [root]
  | _, next, .step walk _ _ => next :: walk.vertices

@[simp]
theorem vertices_nil : (ReducedWalk.nil (graph := graph) (root := root)).vertices =
    [root] :=
  rfl

@[simp]
theorem vertices_step {previous : Option Vertex} {current next : Vertex}
    (walk : ReducedWalk graph root previous current)
    (adjacent : graph.Adj current next)
    (notBacktrack : previous ≠ some next) :
    (ReducedWalk.step walk adjacent notBacktrack).vertices =
      next :: walk.vertices :=
  rfl

@[simp]
theorem vertices_ne_nil {previous : Option Vertex} {current : Vertex}
    (walk : ReducedWalk graph root previous current) :
    walk.vertices ≠ [] := by
  cases walk <;> simp

/-- When the previous endpoint of a nonempty reduced walk is specified, it is
adjacent to the current endpoint. -/
theorem current_adj_previous {previous : Option Vertex} {current prior : Vertex}
    (walk : ReducedWalk graph root previous current)
    (previousEquals : previous = some prior) : graph.Adj current prior := by
  cases walk with
  | nil => simp at previousEquals
  | step walk adjacent notBacktrack =>
      cases previousEquals
      exact adjacent.symm

/-- Apply an automorphism of the base graph to every vertex and edge of a
reduced walk. -/
def mapIso (automorphism : graph ≃g graph) :
    {previous : Option Vertex} → {current : Vertex} →
      ReducedWalk graph root previous current →
        ReducedWalk graph (automorphism root) (previous.map automorphism)
          (automorphism current)
  | _, _, .nil => .nil
  | _, _, .step (previous := before) walk adjacent notBacktrack =>
      .step (mapIso automorphism walk)
        (automorphism.map_adj_iff.mpr adjacent) (by
          cases before with
          | none => simp
          | some previous =>
              simp only [Option.map_some, ne_eq, Option.some.injEq]
              intro equality
              exact notBacktrack <| congrArg some <|
                automorphism.injective equality)

end ReducedWalk

/-- A vertex of the universal tree is a reduced walk together with its two
endpoint indices. -/
structure UniversalVertex where
  previous : Option Vertex
  current : Vertex
  walk : ReducedWalk graph root previous current
  deriving Countable

namespace UniversalVertex

/-- Projection of the universal tree to the base graph. -/
def endpoint (point : UniversalVertex graph root) : Vertex :=
  point.current

/-- The trivial walk above the chosen base vertex. -/
def base : UniversalVertex graph root :=
  ⟨none, root, .nil⟩

/-- Distance from a universal-cover vertex to the chosen lift of the base
vertex. -/
def depth (point : UniversalVertex graph root) : ℕ :=
  point.walk.length

/-- A reduced-walk vertex at depth zero is the distinguished base vertex. -/
theorem eq_base_of_depth_eq_zero (point : UniversalVertex graph root)
    (depthEqualsZero : point.depth = 0) : point = base graph root := by
  rcases point with ⟨previous, current, walk⟩
  cases walk with
  | nil => rfl
  | step walk adjacent notBacktrack =>
      have impossible : False := Nat.succ_ne_zero walk.length <| by
        simpa only [depth, ReducedWalk.length, Nat.succ_eq_add_one]
          using depthEqualsZero
      exact impossible.elim

/-- Delete the final step of a nontrivial reduced walk. -/
def parent : UniversalVertex graph root → Option (UniversalVertex graph root)
  | ⟨none, _, .nil⟩ => none
  | ⟨some previous, _, .step (previous := before) walk _ _⟩ =>
      some ⟨before, previous, walk⟩

@[simp]
theorem parent_base : (base graph root).parent = none :=
  rfl

@[simp]
theorem parent_step {previous : Option Vertex} {current next : Vertex}
    (walk : ReducedWalk graph root previous current)
    (adjacent : graph.Adj current next)
    (notBacktrack : previous ≠ some next) :
    (UniversalVertex.mk (some current) next
      (.step walk adjacent notBacktrack)).parent =
        some (UniversalVertex.mk previous current walk) :=
  rfl

/-- Lift one adjacent base vertex.  Moving back to the previous endpoint
deletes the final step; every other move appends a new reduced step. -/
noncomputable def liftNeighbor
    (point : UniversalVertex graph root) (next : Vertex)
    (adjacent : graph.Adj point.endpoint next) :
    UniversalVertex graph root := by
  classical
  rcases point with ⟨previous, current, walk⟩
  cases walk with
  | nil =>
      exact ⟨some root, next, .step .nil adjacent (by simp)⟩
  | @step before prior current parentWalk parentAdjacent notBacktrack =>
      by_cases backtracks : next = prior
      · exact ⟨before, prior, parentWalk⟩
      · exact ⟨some current, next,
          .step (.step parentWalk parentAdjacent notBacktrack) adjacent
            (by
              intro equality
              exact backtracks (Option.some.inj equality).symm)⟩

@[simp]
theorem liftNeighbor_endpoint
    (point : UniversalVertex graph root) (next : Vertex)
    (adjacent : graph.Adj point.endpoint next) :
    (liftNeighbor graph root point next adjacent).endpoint = next := by
  classical
  rcases point with ⟨previous, current, walk⟩
  cases walk with
  | nil => rfl
  | @step before prior current parentWalk parentAdjacent notBacktrack =>
      simp only [liftNeighbor]
      split
      next backtracks => exact backtracks.symm
      next _ => rfl

/-- The parent relation, symmetrized below to form the universal tree. -/
def IsChild (first second : UniversalVertex graph root) : Prop :=
  second.parent = some first

/-- The rooted tree of reduced walks. -/
def tree : SimpleGraph (UniversalVertex graph root) :=
  SimpleGraph.fromRel (IsChild graph root)

theorem tree_adj_iff {first second : UniversalVertex graph root} :
    (tree graph root).Adj first second ↔
      first ≠ second ∧
        (second.parent = some first ∨ first.parent = some second) := by
  rw [tree, SimpleGraph.fromRel_adj]
  rfl

/-- The lifted neighbor is adjacent to the starting universal vertex. -/
theorem adjacent_liftNeighbor
    (point : UniversalVertex graph root) (next : Vertex)
    (adjacent : graph.Adj point.endpoint next) :
    (tree graph root).Adj point
      (liftNeighbor graph root point next adjacent) := by
  classical
  rw [tree_adj_iff]
  constructor
  · intro equality
    have endpointEquality := congrArg (endpoint graph root) equality
    rw [liftNeighbor_endpoint] at endpointEquality
    exact adjacent.ne endpointEquality
  · rcases point with ⟨previous, current, walk⟩
    cases walk with
    | nil =>
        left
        rfl
    | @step before prior current parentWalk parentAdjacent notBacktrack =>
        simp only [liftNeighbor]
        split
        next backtracks =>
          right
          subst next
          rfl
        next _ =>
          left
          rfl

/-- A parent step projects to an edge of the base graph. -/
theorem endpoint_adj_of_parent {first second : UniversalVertex graph root}
    (parent : second.parent = some first) :
    graph.Adj first.endpoint second.endpoint := by
  rcases second with ⟨previous, current, walk⟩
  cases walk with
  | nil => simp [UniversalVertex.parent] at parent
  | @step before prior next walk adjacent notBacktrack =>
      simp only [UniversalVertex.parent, Option.some.injEq] at parent
      cases parent
      exact adjacent

/-- Parent edges lower the reduced-walk depth by exactly one. -/
theorem depth_eq_parent_add_one {parentPoint child : UniversalVertex graph root}
    (parent : child.parent = some parentPoint) :
    child.depth = parentPoint.depth + 1 := by
  rcases child with ⟨previous, current, walk⟩
  cases walk with
  | nil => simp [UniversalVertex.parent] at parent
  | @step before prior next walk adjacent notBacktrack =>
      simp only [UniversalVertex.parent, Option.some.injEq] at parent
      cases parent
      rfl

/-- Every universal-tree edge projects to an edge of the base graph. -/
theorem endpoint_adj {first second : UniversalVertex graph root}
    (adjacent : (tree graph root).Adj first second) :
    graph.Adj first.endpoint second.endpoint := by
  rcases tree_adj_iff (graph := graph) (root := root).mp adjacent with
    ⟨_, parent | parent⟩
  · exact endpoint_adj_of_parent graph root parent
  · exact (endpoint_adj_of_parent graph root parent).symm

/-- At most one adjacent vertex has depth no greater than the current
vertex: it is the parent. -/
theorem parent_eq_of_adj_of_depth_le
    {point neighbor : UniversalVertex graph root}
    (adjacent : (tree graph root).Adj point neighbor)
    (depth_le : neighbor.depth ≤ point.depth) :
    point.parent = some neighbor := by
  rcases (tree_adj_iff (graph := graph) (root := root)).mp adjacent with
    ⟨_, neighborChild | pointChild⟩
  · have depth_eq := depth_eq_parent_add_one graph root neighborChild
    omega
  · exact pointChild

/-- Two adjacent vertices of no greater depth than a fixed point coincide. -/
theorem lower_neighbor_unique
    {point first second : UniversalVertex graph root}
    (firstAdjacent : (tree graph root).Adj point first)
    (secondAdjacent : (tree graph root).Adj point second)
    (firstDepth : first.depth ≤ point.depth)
    (secondDepth : second.depth ≤ point.depth) :
    first = second := by
  have firstParent := parent_eq_of_adj_of_depth_le graph root
    firstAdjacent firstDepth
  have secondParent := parent_eq_of_adj_of_depth_le graph root
    secondAdjacent secondDepth
  exact Option.some.inj (firstParent.symm.trans secondParent)

/-- Local uniqueness of path lifting: an adjacent universal vertex is the
canonical lift of its projected endpoint. -/
theorem liftNeighbor_eq_of_adj
    (point neighbor : UniversalVertex graph root)
    (adjacent : (tree graph root).Adj point neighbor) :
    liftNeighbor graph root point neighbor.endpoint
        (endpoint_adj graph root adjacent) = neighbor := by
  classical
  rcases (tree_adj_iff (graph := graph) (root := root)).mp adjacent with
    ⟨_, neighborChild | pointChild⟩
  · rcases neighbor with ⟨neighborPrevious, neighborCurrent, neighborWalk⟩
    cases neighborWalk with
    | nil => simp [parent] at neighborChild
    | @step before prior current parentWalk parentAdjacent notBacktrack =>
        simp only [parent, Option.some.injEq] at neighborChild
        cases neighborChild
        cases parentWalk with
        | nil =>
            rfl
        | @step parentBefore grandparent prior grandparentWalk
            grandparentAdjacent parentNotBacktrack =>
            simp only [liftNeighbor]
            rw [dif_neg]
            · rfl
            · intro backtracks
              apply notBacktrack
              exact congrArg some backtracks.symm
  · rcases point with ⟨pointPrevious, pointCurrent, pointWalk⟩
    cases pointWalk with
    | nil => simp [parent] at pointChild
    | @step before prior current parentWalk parentAdjacent notBacktrack =>
        simp only [parent, Option.some.injEq] at pointChild
        cases pointChild
        change liftNeighbor graph root
          (UniversalVertex.mk (some prior) pointCurrent
            (.step parentWalk parentAdjacent notBacktrack))
          prior _ = UniversalVertex.mk before prior parentWalk
        simp only [liftNeighbor]
        simp

/-- Local path-lifting uniqueness with the target endpoint supplied separately.
This form avoids transporting dependent adjacency proofs through endpoint
equalities. -/
theorem liftNeighbor_eq_of_adj_of_endpoint_eq
    (point neighbor : UniversalVertex graph root) (next : Vertex)
    (baseAdjacent : graph.Adj point.endpoint next)
    (universalAdjacent : (tree graph root).Adj point neighbor)
    (endpoint_eq : neighbor.endpoint = next) :
    liftNeighbor graph root point next baseAdjacent = neighbor := by
  subst next
  simpa using liftNeighbor_eq_of_adj graph root point neighbor universalAdjacent

/-- Two neighbors of one universal vertex coincide as soon as their projected
endpoints coincide. -/
theorem neighbor_eq_of_endpoint_eq
    {point first second : UniversalVertex graph root}
    (firstAdjacent : (tree graph root).Adj point first)
    (secondAdjacent : (tree graph root).Adj point second)
    (endpoint_eq : first.endpoint = second.endpoint) :
    first = second := by
  have first_eq :
      liftNeighbor graph root point second.endpoint
          (by simpa [endpoint_eq] using endpoint_adj graph root firstAdjacent) =
        first :=
    liftNeighbor_eq_of_adj_of_endpoint_eq graph root point first
      second.endpoint _ firstAdjacent endpoint_eq
  have second_eq :
      liftNeighbor graph root point second.endpoint
          (endpoint_adj graph root secondAdjacent) = second :=
    liftNeighbor_eq_of_adj graph root point second secondAdjacent
  exact first_eq.symm.trans second_eq

/-- Lifting an edge and immediately lifting its reverse returns to the
starting universal vertex. -/
theorem liftNeighbor_involutive
    (point : UniversalVertex graph root) (next : Vertex)
    (adjacent : graph.Adj point.endpoint next) :
    liftNeighbor graph root
        (liftNeighbor graph root point next adjacent)
        point.endpoint
        (by
          rw [liftNeighbor_endpoint]
          exact adjacent.symm) = point := by
  apply liftNeighbor_eq_of_adj graph root
  exact (adjacent_liftNeighbor graph root point next adjacent).symm

/-- The endpoint projection is locally bijective.  This is the graph-level
covering law used when the walk tree is converted back to a source
semi-graph. -/
noncomputable def neighborEquiv (point : UniversalVertex graph root) :
    graph.neighborSet point.endpoint ≃
      (tree graph root).neighborSet point where
  toFun next :=
    ⟨liftNeighbor graph root point next.1 next.2,
      adjacent_liftNeighbor graph root point next.1 next.2⟩
  invFun neighbor :=
    ⟨neighbor.1.endpoint, endpoint_adj graph root neighbor.2⟩
  left_inv next := by
    apply Subtype.ext
    exact liftNeighbor_endpoint graph root point next.1 next.2
  right_inv neighbor := by
    apply Subtype.ext
    exact liftNeighbor_eq_of_adj graph root point neighbor.1 neighbor.2

/-- The unique chain of parent edges from a reduced walk back to the chosen
lift of the base vertex. -/
def walkToBase : (point : UniversalVertex graph root) →
    (tree graph root).Walk point (base graph root)
  | ⟨none, _, .nil⟩ => .nil
  | ⟨some prior, current,
      .step (previous := before) parentWalk adjacent notBacktrack⟩ =>
      .cons (by
        rw [tree_adj_iff]
        constructor
        · intro equality
          have endpointEquality := congrArg (endpoint graph root) equality
          exact adjacent.ne endpointEquality.symm
        · right
          rfl)
        (walkToBase ⟨before, prior, parentWalk⟩)

/-- The reduced-walk universal cover is connected. -/
theorem tree_connected : (tree graph root).Connected := by
  letI : Nonempty (UniversalVertex graph root) := ⟨base graph root⟩
  exact ⟨fun first second =>
    ⟨(walkToBase graph root first).append
      (walkToBase graph root second).reverse⟩⟩

/-- The reduced-walk tree has no cycles.  At a maximum-depth vertex of a
putative cycle, both cycle neighbors would have to be the unique parent. -/
theorem tree_isAcyclic : (tree graph root).IsAcyclic := by
  classical
  intro start cycle cycleIsCycle
  obtain ⟨maximum, maximum_mem, maximum_spec⟩ :=
    Finset.exists_max_image cycle.support.toFinset
      (depth graph root) (by simp)
  have maximum_mem_support : maximum ∈ cycle.support := by
    simpa using maximum_mem
  let rotated := cycle.rotate maximum maximum_mem_support
  have rotatedIsCycle : rotated.IsCycle :=
    cycleIsCycle.rotate maximum_mem_support
  have rotatedNotNil : ¬rotated.Nil := rotatedIsCycle.not_nil
  have second_mem_support : rotated.snd ∈ cycle.support :=
    (cycle.mem_support_rotate_iff maximum maximum_mem_support).mp
      (rotated.getVert_mem_support 1)
  have penultimate_mem_support : rotated.penultimate ∈ cycle.support :=
    (cycle.mem_support_rotate_iff maximum maximum_mem_support).mp
      (rotated.getVert_mem_support (rotated.length - 1))
  have second_depth :
      (depth graph root rotated.snd) ≤ depth graph root maximum :=
    maximum_spec rotated.snd (by simpa using second_mem_support)
  have penultimate_depth :
      (depth graph root rotated.penultimate) ≤ depth graph root maximum :=
    maximum_spec rotated.penultimate (by simpa using penultimate_mem_support)
  have neighbors_equal : rotated.snd = rotated.penultimate :=
    lower_neighbor_unique graph root
      (rotated.adj_snd rotatedNotNil)
      (rotated.adj_penultimate rotatedNotNil).symm
      second_depth penultimate_depth
  exact rotatedIsCycle.snd_ne_penultimate neighbors_equal

/-- The combinatorial universal cover is a connected tree. -/
theorem tree_isTree : (tree graph root).IsTree where
  connected := tree_connected graph root
  isAcyclic := tree_isAcyclic graph root

/-- The endpoint projection as a graph homomorphism. -/
def projection : tree graph root →g graph where
  toFun := endpoint graph root
  map_rel' := endpoint_adj graph root

/-- Map a reduced source walk along an arbitrary graph homomorphism, reducing
backtracking in the target as it appears.  `liftNeighbor` performs exactly one
append-or-cancel step, so no quotient of walks is needed. -/
noncomputable def mapHomWalk {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph) :
    {previous : Option Vertex} → {current : Vertex} →
      ReducedWalk graph root previous current →
        {point : UniversalVertex targetGraph (hom root) //
          point.endpoint = hom current}
  | _, _, .nil => ⟨base targetGraph (hom root), rfl⟩
  | _, next, .step walk adjacent _ =>
      let mapped := mapHomWalk targetGraph hom walk
      ⟨liftNeighbor targetGraph (hom root) mapped.1 (hom next) (by
          rw [mapped.2]
          exact hom.map_rel adjacent),
        liftNeighbor_endpoint targetGraph (hom root) _ _ _⟩

/-- The canonical lift of a graph homomorphism to the two reduced-walk
universal trees. -/
noncomputable def mapHom {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph) :
    UniversalVertex graph root → UniversalVertex targetGraph (hom root)
  | ⟨_, _, walk⟩ => (mapHomWalk graph root targetGraph hom walk).1

/-- A graph homomorphism is locally injective when two neighbors of the same
vertex with equal images were already equal. -/
def IsLocallyInjective {Target : Type u} (targetGraph : SimpleGraph Target)
    (hom : graph →g targetGraph) : Prop :=
  ∀ {center first second : Vertex},
    graph.Adj center first → graph.Adj center second →
      hom first = hom second → first = second

/-- A locally injective graph homomorphism maps a reduced walk without
introducing any cancellation. -/
def mapReducedWalkOfLocallyInjective {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom) :
    {previous : Option Vertex} → {current : Vertex} →
      ReducedWalk graph root previous current →
        ReducedWalk targetGraph (hom root) (previous.map hom) (hom current)
  | _, _, .nil => .nil
  | _, _, .step (previous := previous) walk adjacent notBacktrack =>
      .step (mapReducedWalkOfLocallyInjective targetGraph hom locallyInjective walk)
        (hom.map_rel adjacent) (by
          cases previous with
          | none => simp
          | some prior =>
              simp only [Option.map_some, ne_eq, Option.some.injEq]
              intro mappedEquality
              apply notBacktrack
              apply congrArg some
              exact locallyInjective
                (ReducedWalk.current_adj_previous graph root walk rfl)
                adjacent mappedEquality)

/-- The cancellation-free universal-tree map supplied by a locally injective
base-graph homomorphism. -/
def mapHomOfLocallyInjective {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom) :
    UniversalVertex graph root → UniversalVertex targetGraph (hom root)
  | ⟨previous, current, walk⟩ =>
      ⟨previous.map hom, hom current,
        mapReducedWalkOfLocallyInjective graph root targetGraph hom
          locallyInjective walk⟩

@[simp]
theorem mapHomOfLocallyInjective_endpoint {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom)
    (point : UniversalVertex graph root) :
    (mapHomOfLocallyInjective graph root targetGraph hom locallyInjective point).endpoint =
      hom point.endpoint :=
  rfl

@[simp]
theorem mapHomOfLocallyInjective_base {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom) :
    mapHomOfLocallyInjective graph root targetGraph hom locallyInjective
        (base graph root) =
      base targetGraph (hom root) :=
  rfl

@[simp]
theorem mapHomOfLocallyInjective_parent {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom)
    (point : UniversalVertex graph root) :
    (mapHomOfLocallyInjective graph root targetGraph hom locallyInjective point).parent =
      point.parent.map
        (mapHomOfLocallyInjective graph root targetGraph hom locallyInjective) := by
  rcases point with ⟨previous, current, walk⟩
  cases walk <;> rfl

@[simp]
theorem mapHomOfLocallyInjective_depth {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom)
    (point : UniversalVertex graph root) :
    (mapHomOfLocallyInjective graph root targetGraph hom
      locallyInjective point).depth = point.depth := by
  rcases point with ⟨previous, current, walk⟩
  induction walk with
  | nil => rfl
  | step walk adjacent notBacktrack inductionHypothesis =>
      simpa only [mapHomOfLocallyInjective, mapReducedWalkOfLocallyInjective,
        depth, ReducedWalk.length] using congrArg (fun value => value + 1)
          inductionHypothesis

/-- The cancellation-free lift preserves universal-tree adjacency. -/
theorem mapHomOfLocallyInjective_adj {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom)
    {first second : UniversalVertex graph root}
    (adjacent : (tree graph root).Adj first second) :
    (tree targetGraph (hom root)).Adj
      (mapHomOfLocallyInjective graph root targetGraph hom locallyInjective first)
      (mapHomOfLocallyInjective graph root targetGraph hom locallyInjective second) := by
  rw [tree_adj_iff]
  constructor
  · intro equality
    have endpointEquality := congrArg (endpoint targetGraph (hom root)) equality
    simp only [mapHomOfLocallyInjective_endpoint] at endpointEquality
    exact (hom.map_rel (endpoint_adj graph root adjacent)).ne endpointEquality
  · rcases (tree_adj_iff (graph := graph) (root := root)).mp adjacent with
      ⟨_, secondChild | firstChild⟩
    · left
      rw [mapHomOfLocallyInjective_parent, secondChild]
      rfl
    · right
      rw [mapHomOfLocallyInjective_parent, firstChild]
      rfl

/-- A locally injective base-graph homomorphism induces an injective map of
the corresponding universal trees. -/
theorem mapHomOfLocallyInjective_injective {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom) :
    Function.Injective
      (mapHomOfLocallyInjective graph root targetGraph hom locallyInjective) := by
  intro first second mappedEquality
  rcases first with ⟨firstPrevious, firstCurrent, firstWalk⟩
  induction firstWalk generalizing second with
  | nil =>
      have depthEquality := congrArg (depth targetGraph (hom root)) mappedEquality
      simp only [mapHomOfLocallyInjective_depth] at depthEquality
      have secondIsBase := eq_base_of_depth_eq_zero graph root second depthEquality.symm
      rw [secondIsBase]
      rfl
  | @step before prior next firstParentWalk firstAdjacent firstNotBacktrack
      inductionHypothesis =>
      rcases second with ⟨secondPrevious, secondCurrent, secondWalk⟩
      cases secondWalk with
      | nil =>
          have depthEquality := congrArg (depth targetGraph (hom root)) mappedEquality
          rw [mapHomOfLocallyInjective_depth,
            mapHomOfLocallyInjective_depth] at depthEquality
          change firstParentWalk.length + 1 = 0 at depthEquality
          omega
      | @step secondBefore secondPrior secondNext secondParentWalk
          secondAdjacent secondNotBacktrack =>
          let firstParent : UniversalVertex graph root :=
            ⟨before, prior, firstParentWalk⟩
          let secondParent : UniversalVertex graph root :=
            ⟨secondBefore, secondPrior, secondParentWalk⟩
          have mappedParentEquality :
              mapHomOfLocallyInjective graph root targetGraph hom locallyInjective
                  firstParent =
                mapHomOfLocallyInjective graph root targetGraph hom locallyInjective
                  secondParent := by
            have parentEquality := congrArg (parent targetGraph (hom root))
              mappedEquality
            change some
                (mapHomOfLocallyInjective graph root targetGraph hom
                  locallyInjective firstParent) =
              some
                (mapHomOfLocallyInjective graph root targetGraph hom
                  locallyInjective secondParent) at parentEquality
            exact Option.some.inj parentEquality
          have parentEquality : firstParent = secondParent :=
            inductionHypothesis mappedParentEquality
          have mappedEndpointEquality := congrArg
            (endpoint targetGraph (hom root)) mappedEquality
          change hom next = hom secondCurrent at mappedEndpointEquality
          have parentEndpointEquality : prior = secondPrior :=
            congrArg (endpoint graph root) parentEquality
          have secondAdjacentFromFirst : graph.Adj prior secondCurrent := by
            rw [parentEndpointEquality]
            exact secondAdjacent
          have endpointEquality : next = secondCurrent :=
            locallyInjective firstAdjacent secondAdjacentFromFirst
              mappedEndpointEquality
          have firstUniversalAdjacent :
              (tree graph root).Adj firstParent
                ⟨some prior, next,
                  .step firstParentWalk firstAdjacent firstNotBacktrack⟩ := by
            rw [tree_adj_iff]
            exact ⟨by
              intro equality
              exact firstAdjacent.ne <|
                congrArg (endpoint graph root) equality,
              Or.inl rfl⟩
          have secondUniversalAdjacent :
              (tree graph root).Adj firstParent
                ⟨some secondPrior, secondCurrent,
                  .step secondParentWalk secondAdjacent secondNotBacktrack⟩ := by
            rw [parentEquality]
            rw [tree_adj_iff]
            exact ⟨by
              intro equality
              exact secondAdjacent.ne <|
                congrArg (endpoint graph root) equality,
              Or.inl rfl⟩
          exact neighbor_eq_of_endpoint_eq graph root firstUniversalAdjacent
            secondUniversalAdjacent endpointEquality

@[simp]
theorem mapHom_endpoint {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (point : UniversalVertex graph root) :
    (mapHom graph root targetGraph hom point).endpoint = hom point.endpoint := by
  rcases point with ⟨_, _, walk⟩
  exact (mapHomWalk graph root targetGraph hom walk).2

@[simp]
theorem mapHom_base {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph) :
    mapHom graph root targetGraph hom (base graph root) =
      base targetGraph (hom root) :=
  rfl

/-- Mapping by a graph homomorphism preserves each parent edge, even when the
mapped reduced walk cancels its last step. -/
theorem mapHom_adj_of_parent {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    {first second : UniversalVertex graph root}
    (parentLaw : second.parent = some first) :
    (tree targetGraph (hom root)).Adj
      (mapHom graph root targetGraph hom first)
      (mapHom graph root targetGraph hom second) := by
  rcases second with ⟨previous, current, walk⟩
  cases walk with
  | nil => simp [parent] at parentLaw
  | @step before prior current parentWalk adjacent notBacktrack =>
      simp only [parent, Option.some.injEq] at parentLaw
      cases parentLaw
      change (tree targetGraph (hom root)).Adj
        (mapHom graph root targetGraph hom
          ⟨before, prior, parentWalk⟩)
        (liftNeighbor targetGraph (hom root)
          (mapHom graph root targetGraph hom
            ⟨before, prior, parentWalk⟩)
          (hom current) _)
      exact adjacent_liftNeighbor targetGraph (hom root) _ _ _

/-- The canonical universal-tree lift of a graph homomorphism is itself a
graph homomorphism. -/
theorem mapHom_adj {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    {first second : UniversalVertex graph root}
    (adjacent : (tree graph root).Adj first second) :
    (tree targetGraph (hom root)).Adj
      (mapHom graph root targetGraph hom first)
      (mapHom graph root targetGraph hom second) := by
  rcases (tree_adj_iff (graph := graph) (root := root)).mp adjacent with
    ⟨_, secondChild | firstChild⟩
  · exact mapHom_adj_of_parent graph root targetGraph hom secondChild
  · exact (mapHom_adj_of_parent graph root targetGraph hom firstChild).symm

/-- The lifted map between universal trees. -/
noncomputable def universalMapHom {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph) :
    tree graph root →g tree targetGraph (hom root) where
  toFun := mapHom graph root targetGraph hom
  map_rel' := mapHom_adj graph root targetGraph hom

/-- Apply a base-graph automorphism to a universal reduced walk. -/
def mapIso (automorphism : graph ≃g graph)
    (point : UniversalVertex graph root) :
    UniversalVertex graph (automorphism root) :=
  ⟨point.previous.map automorphism, automorphism point.current,
    ReducedWalk.mapIso graph root automorphism point.walk⟩

@[simp]
theorem mapIso_endpoint (automorphism : graph ≃g graph)
    (point : UniversalVertex graph root) :
    (mapIso graph root automorphism point).endpoint =
      automorphism point.endpoint :=
  rfl

@[simp]
theorem mapIso_base (automorphism : graph ≃g graph) :
    mapIso graph root automorphism (base graph root) =
      base graph (automorphism root) :=
  rfl

/-- Mapping by a base automorphism preserves a parent edge. -/
theorem mapIso_adj_of_parent (automorphism : graph ≃g graph)
    {first second : UniversalVertex graph root}
    (parentLaw : second.parent = some first) :
    (tree graph (automorphism root)).Adj
      (mapIso graph root automorphism first)
      (mapIso graph root automorphism second) := by
  rcases second with ⟨previous, current, walk⟩
  cases walk with
  | nil => simp [parent] at parentLaw
  | @step before prior current parentWalk adjacent notBacktrack =>
      simp only [parent, Option.some.injEq] at parentLaw
      cases parentLaw
      rw [tree_adj_iff]
      constructor
      · intro equality
        have endpointEquality := congrArg
          (endpoint graph (automorphism root)) equality
        change automorphism prior = automorphism current at endpointEquality
        exact (automorphism.map_adj_iff.mpr adjacent).ne endpointEquality
      · left
        rfl

/-- Mapping by a base automorphism is a graph homomorphism. -/
theorem mapIso_adj (automorphism : graph ≃g graph)
    {first second : UniversalVertex graph root}
    (adjacent : (tree graph root).Adj first second) :
    (tree graph (automorphism root)).Adj
      (mapIso graph root automorphism first)
      (mapIso graph root automorphism second) := by
  rcases (tree_adj_iff (graph := graph) (root := root)).mp adjacent with
    ⟨_, secondChild | firstChild⟩
  · exact mapIso_adj_of_parent graph root automorphism secondChild
  · exact (mapIso_adj_of_parent graph root automorphism firstChild).symm

/-- Lift a reduced walk based at `point.endpoint` into the universal tree,
starting at `point`. -/
noncomputable def liftReducedWalkFrom
    (point : UniversalVertex graph root) :
    {previous : Option Vertex} → {current : Vertex} →
      ReducedWalk graph point.endpoint previous current →
        {target : UniversalVertex graph root // target.endpoint = current}
  | _, _, .nil => ⟨point, rfl⟩
  | _, next, .step walk adjacent notBacktrack =>
      let lifted := liftReducedWalkFrom point walk
      ⟨liftNeighbor graph root lifted.1 next (by
          rw [lifted.2]
          exact adjacent),
        liftNeighbor_endpoint graph root _ _ _⟩

/-- Change the chosen root of a reduced-walk tree by lifting every reduced
walk from a specified point over the new root. -/
noncomputable def rerootMap (point : UniversalVertex graph root) :
    UniversalVertex graph point.endpoint → UniversalVertex graph root
  | source => (liftReducedWalkFrom graph root point source.walk).1

@[simp]
theorem rerootMap_endpoint (point : UniversalVertex graph root)
    (source : UniversalVertex graph point.endpoint) :
    (rerootMap graph root point source).endpoint = source.endpoint :=
  (liftReducedWalkFrom graph root point source.walk).2

@[simp]
theorem rerootMap_base (point : UniversalVertex graph root) :
    rerootMap graph root point (base graph point.endpoint) = point :=
  rfl

/-- Rerooting preserves a parent edge. -/
theorem rerootMap_adj_of_parent (point : UniversalVertex graph root)
    {first second : UniversalVertex graph point.endpoint}
    (parentLaw : second.parent = some first) :
    (tree graph root).Adj (rerootMap graph root point first)
      (rerootMap graph root point second) := by
  rcases second with ⟨previous, current, walk⟩
  cases walk with
  | nil => simp [parent] at parentLaw
  | @step before prior current parentWalk adjacent notBacktrack =>
      simp only [parent, Option.some.injEq] at parentLaw
      cases parentLaw
      change (tree graph root).Adj
        (rerootMap graph root point ⟨before, prior, parentWalk⟩)
        (liftNeighbor graph root
          (rerootMap graph root point ⟨before, prior, parentWalk⟩)
          current _)
      exact adjacent_liftNeighbor graph root _ _ _

/-- Rerooting is a graph homomorphism. -/
theorem rerootMap_adj (point : UniversalVertex graph root)
    {first second : UniversalVertex graph point.endpoint}
    (adjacent : (tree graph point.endpoint).Adj first second) :
    (tree graph root).Adj (rerootMap graph root point first)
      (rerootMap graph root point second) := by
  rcases (tree_adj_iff (graph := graph) (root := point.endpoint)).mp adjacent with
    ⟨_, secondChild | firstChild⟩
  · exact rerootMap_adj_of_parent graph root point secondChild
  · exact (rerootMap_adj_of_parent graph root point firstChild).symm

/-- Two graph maps from one universal tree into another agree once their
target endpoints agree everywhere and their values agree at one point. -/
theorem map_eq_of_endpoint_eq_adj
    {Source Target : Type u} (sourceGraph : SimpleGraph Source)
    (sourceRoot : Source) (targetGraph : SimpleGraph Target)
    (targetRoot : Target)
    (first second : UniversalVertex sourceGraph sourceRoot →
      UniversalVertex targetGraph targetRoot)
    (endpointEquality : ∀ point,
      (first point).endpoint = (second point).endpoint)
    (firstAdjacent : ∀ {point neighbor},
      (tree sourceGraph sourceRoot).Adj point neighbor →
        (tree targetGraph targetRoot).Adj (first point) (first neighbor))
    (secondAdjacent : ∀ {point neighbor},
      (tree sourceGraph sourceRoot).Adj point neighbor →
        (tree targetGraph targetRoot).Adj (second point) (second neighbor))
    (point : UniversalVertex sourceGraph sourceRoot)
    (atPoint : first point = second point) : first = second := by
  funext target
  obtain ⟨walk⟩ := (tree_connected sourceGraph sourceRoot) point target
  have alongWalk : ∀ {source destination}
      (path : (tree sourceGraph sourceRoot).Walk source destination),
      first source = second source → first destination = second destination := by
    intro source destination path
    induction path with
    | nil => exact id
    | @cons source neighbor destination adjacent tail inductionHypothesis =>
        intro atSource
        have mappedFirst :
            (tree targetGraph targetRoot).Adj
              (first source) (first neighbor) :=
          firstAdjacent adjacent
        have mappedSecond :
            (tree targetGraph targetRoot).Adj
              (first source) (second neighbor) := by
          rw [atSource]
          exact secondAdjacent adjacent
        exact inductionHypothesis <|
          neighbor_eq_of_endpoint_eq targetGraph targetRoot
            mappedFirst mappedSecond (endpointEquality neighbor)
  exact alongWalk walk atPoint

/-- For a locally injective graph homomorphism, the general universal-tree map
is the cancellation-free reduced-walk map. -/
theorem mapHom_eq_mapHomOfLocallyInjective {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom) :
    mapHom graph root targetGraph hom =
      mapHomOfLocallyInjective graph root targetGraph hom locallyInjective := by
  apply map_eq_of_endpoint_eq_adj graph root targetGraph (hom root)
    (point := base graph root)
  · intro point
    rw [mapHom_endpoint, mapHomOfLocallyInjective_endpoint]
  · intro point neighbor adjacent
    exact mapHom_adj graph root targetGraph hom adjacent
  · intro point neighbor adjacent
    exact mapHomOfLocallyInjective_adj graph root targetGraph hom
      locallyInjective adjacent
  · rw [mapHom_base, mapHomOfLocallyInjective_base]

/-- Local injectivity on the base graph is enough for injectivity of the
canonical universal-tree map. -/
theorem mapHom_injective_of_locallyInjective {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallyInjective : IsLocallyInjective graph targetGraph hom) :
    Function.Injective (mapHom graph root targetGraph hom) := by
  rw [mapHom_eq_mapHomOfLocallyInjective graph root targetGraph hom
    locallyInjective]
  exact mapHomOfLocallyInjective_injective graph root targetGraph hom
    locallyInjective

/-- Two endpoint-preserving graph maps out of a universal tree agree
everywhere once they agree at one point. -/
theorem map_eq_of_endpoint_adj
    {sourceRoot targetRoot : Vertex}
    (first second : UniversalVertex graph sourceRoot →
      UniversalVertex graph targetRoot)
    (firstEndpoint : ∀ point, (first point).endpoint = point.endpoint)
    (secondEndpoint : ∀ point, (second point).endpoint = point.endpoint)
    (firstAdjacent : ∀ {point neighbor},
      (tree graph sourceRoot).Adj point neighbor →
        (tree graph targetRoot).Adj (first point) (first neighbor))
    (secondAdjacent : ∀ {point neighbor},
      (tree graph sourceRoot).Adj point neighbor →
        (tree graph targetRoot).Adj (second point) (second neighbor))
    (point : UniversalVertex graph sourceRoot)
    (atPoint : first point = second point) : first = second := by
  funext target
  obtain ⟨walk⟩ := (tree_connected graph sourceRoot) point target
  have alongWalk : ∀ {source destination}
      (path : (tree graph sourceRoot).Walk source destination),
      first source = second source → first destination = second destination := by
    intro source destination path
    induction path with
    | nil => exact id
    | @cons source neighbor destination adjacent tail inductionHypothesis =>
        intro atSource
        have mappedFirst :
            (tree graph targetRoot).Adj (first source) (first neighbor) :=
          firstAdjacent adjacent
        have mappedSecond :
            (tree graph targetRoot).Adj (first source) (second neighbor) := by
          rw [atSource]
          exact secondAdjacent adjacent
        have endpointEquality :
            (first neighbor).endpoint = (second neighbor).endpoint :=
          (firstEndpoint neighbor).trans (secondEndpoint neighbor).symm
        exact inductionHypothesis
          (neighbor_eq_of_endpoint_eq graph targetRoot mappedFirst mappedSecond
            endpointEquality)
  exact alongWalk walk atPoint

/-- Every point of the original universal tree has a preimage under
rerooting. -/
theorem rerootMap_surjective (point : UniversalVertex graph root) :
    Function.Surjective (rerootMap graph root point) := by
  intro target
  obtain ⟨walk⟩ := (tree_connected graph root) point target
  have liftAlong : ∀ {source destination}
      (path : (tree graph root).Walk source destination)
      (preimage : UniversalVertex graph point.endpoint),
      rerootMap graph root point preimage = source →
        ∃ result, rerootMap graph root point result = destination := by
    intro source destination path
    induction path with
    | nil =>
        intro preimage equality
        exact ⟨preimage, equality⟩
    | @cons source neighbor destination adjacent tail inductionHypothesis =>
        intro preimage equality
        let next : UniversalVertex graph point.endpoint :=
          liftNeighbor graph point.endpoint preimage neighbor.endpoint (by
            rw [← rerootMap_endpoint graph root point preimage, equality]
            exact endpoint_adj graph root adjacent)
        have nextAdjacent :
            (tree graph point.endpoint).Adj preimage next :=
          adjacent_liftNeighbor graph point.endpoint _ _ _
        have mappedNextAdjacent :
            (tree graph root).Adj source
              (rerootMap graph root point next) := by
          rw [← equality]
          exact rerootMap_adj graph root point nextAdjacent
        have mappedNextEndpoint :
            (rerootMap graph root point next).endpoint = neighbor.endpoint := by
          rw [rerootMap_endpoint]
          exact liftNeighbor_endpoint graph point.endpoint _ _ _
        have mappedNext : rerootMap graph root point next = neighbor :=
          neighbor_eq_of_endpoint_eq graph root mappedNextAdjacent adjacent
            mappedNextEndpoint
        exact inductionHypothesis next mappedNext
  exact liftAlong walk (base graph point.endpoint) (rerootMap_base graph root point)

/-- Transport a universal-tree vertex when only the chosen root changes by
equality. -/
def castRoot {first second : Vertex} (rootsEqual : first = second) :
    UniversalVertex graph first → UniversalVertex graph second := by
  subst second
  exact id

/-- Transport along an equality of roots does not identify distinct universal
tree vertices. -/
theorem castRoot_injective {first second : Vertex}
    (rootsEqual : first = second) :
    Function.Injective (castRoot graph rootsEqual) := by
  subst second
  exact Function.injective_id

@[simp]
theorem castRoot_endpoint {first second : Vertex}
    (rootsEqual : first = second) (point : UniversalVertex graph first) :
    (castRoot graph rootsEqual point).endpoint = point.endpoint := by
  subst second
  rfl

theorem castRoot_adj {first second : Vertex}
    (rootsEqual : first = second) {point neighbor : UniversalVertex graph first}
    (adjacent : (tree graph first).Adj point neighbor) :
    (tree graph second).Adj (castRoot graph rootsEqual point)
      (castRoot graph rootsEqual neighbor) := by
  subst second
  exact adjacent

@[simp]
theorem castRoot_base {first second : Vertex}
    (rootsEqual : first = second) :
    castRoot graph rootsEqual (base graph first) = base graph second := by
  subst second
  rfl

/-- The inverse of mapping universal walks by a base-graph automorphism. -/
def inverseMapIso (automorphism : graph ≃g graph) :
    UniversalVertex graph (automorphism root) → UniversalVertex graph root :=
  fun point => castRoot graph (automorphism.symm_apply_apply root)
    (mapIso graph (automorphism root) automorphism.symm point)

@[simp]
theorem inverseMapIso_endpoint (automorphism : graph ≃g graph)
    (point : UniversalVertex graph (automorphism root)) :
    (inverseMapIso graph root automorphism point).endpoint =
      automorphism.symm point.endpoint := by
  unfold inverseMapIso
  rw [castRoot_endpoint, mapIso_endpoint]

theorem inverseMapIso_adj (automorphism : graph ≃g graph)
    {first second : UniversalVertex graph (automorphism root)}
    (adjacent : (tree graph (automorphism root)).Adj first second) :
    (tree graph root).Adj
      (inverseMapIso graph root automorphism first)
      (inverseMapIso graph root automorphism second) := by
  unfold inverseMapIso
  apply castRoot_adj graph _
  exact mapIso_adj graph (automorphism root) automorphism.symm adjacent

@[simp]
theorem inverseMapIso_base (automorphism : graph ≃g graph) :
    inverseMapIso graph root automorphism (base graph (automorphism root)) =
      base graph root := by
  unfold inverseMapIso
  rw [mapIso_base, castRoot_base]

/-- Mapping walks by a base automorphism and its inverse are mutually
inverse. -/
theorem mapIso_leftInverse (automorphism : graph ≃g graph) :
    Function.LeftInverse (inverseMapIso graph root automorphism)
      (mapIso graph root automorphism) := by
  have mapsEqual :
      (fun point => inverseMapIso graph root automorphism
        (mapIso graph root automorphism point)) = id := by
    apply map_eq_of_endpoint_adj graph (point := base graph root)
    · intro point
      rw [inverseMapIso_endpoint, mapIso_endpoint,
        automorphism.symm_apply_apply]
    · intro point
      rfl
    · intro point neighbor adjacent
      exact inverseMapIso_adj graph root automorphism
        (mapIso_adj graph root automorphism adjacent)
    · intro point neighbor adjacent
      exact adjacent
    · rw [mapIso_base, inverseMapIso_base]
      rfl
  intro point
  exact congrFun mapsEqual point

theorem mapIso_rightInverse (automorphism : graph ≃g graph) :
    Function.RightInverse (inverseMapIso graph root automorphism)
      (mapIso graph root automorphism) := by
  have mapsEqual :
      (fun point => mapIso graph root automorphism
        (inverseMapIso graph root automorphism point)) = id := by
    apply map_eq_of_endpoint_adj graph
      (point := base graph (automorphism root))
    · intro point
      rw [mapIso_endpoint, inverseMapIso_endpoint,
        automorphism.apply_symm_apply]
    · intro point
      rfl
    · intro point neighbor adjacent
      exact mapIso_adj graph root automorphism
        (inverseMapIso_adj graph root automorphism adjacent)
    · intro point neighbor adjacent
      exact adjacent
    · rw [inverseMapIso_base, mapIso_base]
      rfl
  intro point
  exact congrFun mapsEqual point

/-- A base-graph automorphism induces an isomorphism between the universal
trees rooted at a point and at its image. -/
def universalMapIso (automorphism : graph ≃g graph) :
    tree graph root ≃g tree graph (automorphism root) where
  toFun := mapIso graph root automorphism
  invFun := inverseMapIso graph root automorphism
  left_inv := mapIso_leftInverse graph root automorphism
  right_inv := mapIso_rightInverse graph root automorphism
  map_rel_iff' := by
    intro first second
    constructor
    · intro adjacent
      change (tree graph (automorphism root)).Adj
        (mapIso graph root automorphism first)
        (mapIso graph root automorphism second) at adjacent
      have inverseAdjacent := inverseMapIso_adj graph root automorphism adjacent
      rw [mapIso_leftInverse graph root automorphism first,
        mapIso_leftInverse graph root automorphism second] at inverseAdjacent
      exact inverseAdjacent
    · exact mapIso_adj graph root automorphism

@[simp]
theorem universalMapIso_apply (automorphism : graph ≃g graph)
    (point : UniversalVertex graph root) :
    universalMapIso graph root automorphism point =
      mapIso graph root automorphism point :=
  rfl

/-- Equality of roots induces a graph isomorphism of the corresponding
reduced-walk trees. -/
def castRootIso {first second : Vertex} (rootsEqual : first = second) :
    tree graph first ≃g tree graph second := by
  subst second
  exact SimpleGraph.Iso.refl

@[simp]
theorem castRootIso_apply {first second : Vertex}
    (rootsEqual : first = second) (point : UniversalVertex graph first) :
    castRootIso graph rootsEqual point = castRoot graph rootsEqual point := by
  subst second
  rfl

/-- A selected preimage of the old base point under rerooting. -/
noncomputable def rerootBasePreimage (point : UniversalVertex graph root) :
    UniversalVertex graph point.endpoint :=
  Classical.choose (rerootMap_surjective graph root point (base graph root))

@[simp]
theorem rerootMap_rerootBasePreimage (point : UniversalVertex graph root) :
    rerootMap graph root point (rerootBasePreimage graph root point) =
      base graph root :=
  Classical.choose_spec (rerootMap_surjective graph root point (base graph root))

@[simp]
theorem rerootBasePreimage_endpoint (point : UniversalVertex graph root) :
    (rerootBasePreimage graph root point).endpoint = root := by
  let inversePoint := rerootBasePreimage graph root point
  calc
    inversePoint.endpoint =
        (rerootMap graph root point inversePoint).endpoint :=
      (rerootMap_endpoint graph root point inversePoint).symm
    _ = (base graph root).endpoint := congrArg (endpoint graph root)
      (rerootMap_rerootBasePreimage graph root point)
    _ = root := rfl

/-- The inverse rerooting map, with its domain root transported along the
proved endpoint equality of the selected inverse point. -/
noncomputable def inverseRerootMap (point : UniversalVertex graph root) :
    UniversalVertex graph root → UniversalVertex graph point.endpoint :=
  let inversePoint := rerootBasePreimage graph root point
  fun target => rerootMap graph point.endpoint inversePoint
    (castRoot graph (rerootBasePreimage_endpoint graph root point).symm target)

@[simp]
theorem inverseRerootMap_endpoint (point : UniversalVertex graph root)
    (target : UniversalVertex graph root) :
    (inverseRerootMap graph root point target).endpoint = target.endpoint := by
  unfold inverseRerootMap
  rw [rerootMap_endpoint, castRoot_endpoint]

theorem inverseRerootMap_adj (point : UniversalVertex graph root)
    {first second : UniversalVertex graph root}
    (adjacent : (tree graph root).Adj first second) :
    (tree graph point.endpoint).Adj
      (inverseRerootMap graph root point first)
      (inverseRerootMap graph root point second) := by
  unfold inverseRerootMap
  apply rerootMap_adj graph point.endpoint
  exact castRoot_adj graph _ adjacent

@[simp]
theorem inverseRerootMap_base (point : UniversalVertex graph root) :
    inverseRerootMap graph root point (base graph root) =
      rerootBasePreimage graph root point := by
  unfold inverseRerootMap
  rw [castRoot_base, rerootMap_base]

/-- Rerooting at the chosen inverse base point is a left inverse. -/
theorem rerootMap_leftInverse (point : UniversalVertex graph root) :
    Function.LeftInverse (inverseRerootMap graph root point)
      (rerootMap graph root point) := by
  have mapsEqual :
      (fun source => inverseRerootMap graph root point
        (rerootMap graph root point source)) = id := by
    apply map_eq_of_endpoint_adj graph
      (point := rerootBasePreimage graph root point)
    · intro source
      rw [inverseRerootMap_endpoint, rerootMap_endpoint]
    · intro source
      rfl
    · intro source neighbor adjacent
      exact inverseRerootMap_adj graph root point
        (rerootMap_adj graph root point adjacent)
    · intro source neighbor adjacent
      exact adjacent
    · rw [rerootMap_rerootBasePreimage, inverseRerootMap_base]
      rfl
  intro source
  exact congrFun mapsEqual source

/-- Rerooting at the chosen inverse base point is a right inverse. -/
theorem rerootMap_rightInverse (point : UniversalVertex graph root) :
    Function.RightInverse (inverseRerootMap graph root point)
      (rerootMap graph root point) := by
  have mapsEqual :
      (fun target => rerootMap graph root point
        (inverseRerootMap graph root point target)) = id := by
    apply map_eq_of_endpoint_adj graph (point := base graph root)
    · intro target
      rw [rerootMap_endpoint, inverseRerootMap_endpoint]
    · intro target
      rfl
    · intro source neighbor adjacent
      exact rerootMap_adj graph root point
        (inverseRerootMap_adj graph root point adjacent)
    · intro source neighbor adjacent
      exact adjacent
    · rw [inverseRerootMap_base, rerootMap_rerootBasePreimage]
      rfl
  intro target
  exact congrFun mapsEqual target

/-- Canonical change-of-root isomorphism of reduced-walk universal trees. -/
noncomputable def rerootIso (point : UniversalVertex graph root) :
    tree graph point.endpoint ≃g tree graph root where
  toFun := rerootMap graph root point
  invFun := inverseRerootMap graph root point
  left_inv := rerootMap_leftInverse graph root point
  right_inv := rerootMap_rightInverse graph root point
  map_rel_iff' := by
    intro first second
    constructor
    · intro adjacent
      change (tree graph root).Adj
        (rerootMap graph root point first)
        (rerootMap graph root point second) at adjacent
      have inverseAdjacent := inverseRerootMap_adj graph root point adjacent
      rw [rerootMap_leftInverse graph root point first,
        rerootMap_leftInverse graph root point second] at inverseAdjacent
      exact inverseAdjacent
    · exact rerootMap_adj graph root point

@[simp]
theorem rerootIso_apply (point : UniversalVertex graph root)
    (source : UniversalVertex graph point.endpoint) :
    rerootIso graph root point source = rerootMap graph root point source :=
  rfl

@[simp]
theorem rerootIso_symm_apply (point target : UniversalVertex graph root) :
    (rerootIso graph root point).symm target =
      inverseRerootMap graph root point target :=
  rfl

@[simp]
theorem inverseRerootMap_self (point : UniversalVertex graph root) :
    inverseRerootMap graph root point point = base graph point.endpoint := by
  calc
    inverseRerootMap graph root point point =
        inverseRerootMap graph root point
          (rerootMap graph root point (base graph point.endpoint)) :=
      congrArg (inverseRerootMap graph root point)
        (rerootMap_base graph root point).symm
    _ = base graph point.endpoint :=
      rerootMap_leftInverse graph root point (base graph point.endpoint)

/-- Deck transformations of the reduced-walk cover, defined intrinsically as
the graph automorphisms that commute with endpoint projection. -/
def deckTransformationSubgroup : Subgroup
    (Equiv.Perm (UniversalVertex graph root)) where
  carrier := {transformation |
    (∀ point, (transformation point).endpoint = point.endpoint) ∧
      ∀ first second,
        (tree graph root).Adj (transformation first) (transformation second) ↔
          (tree graph root).Adj first second}
  one_mem' := by simp
  mul_mem' := by
    rintro first second ⟨firstEndpoint, firstAdjacent⟩
      ⟨secondEndpoint, secondAdjacent⟩
    constructor
    · intro point
      exact (firstEndpoint (second point)).trans (secondEndpoint point)
    · intro point neighbor
      exact (firstAdjacent (second point) (second neighbor)).trans
        (secondAdjacent point neighbor)
  inv_mem' := by
    rintro transformation ⟨endpointLaw, adjacencyLaw⟩
    constructor
    · intro point
      have := endpointLaw (transformation⁻¹ point)
      simpa using this.symm
    · intro point neighbor
      have := adjacencyLaw (transformation⁻¹ point)
        (transformation⁻¹ neighbor)
      simpa using this.symm

/-- The discrete deck group of the reduced-walk universal cover. -/
abbrev DeckTransformation := deckTransformationSubgroup graph root

namespace DeckTransformation

variable {graph root}

@[simp]
theorem endpoint_apply (transformation : DeckTransformation graph root)
    (point : UniversalVertex graph root) :
    (transformation.1 point).endpoint = point.endpoint :=
  transformation.2.1 point

theorem adjacency_apply_iff
    (transformation : DeckTransformation graph root)
    (first second : UniversalVertex graph root) :
    (tree graph root).Adj (transformation.1 first) (transformation.1 second) ↔
      (tree graph root).Adj first second :=
  transformation.2.2 first second

/-- The graph isomorphism over the base carrying `first` to `second` when
the two points lie in one endpoint fiber. -/
noncomputable def betweenIso
    (first second : UniversalVertex graph root)
    (sameEndpoint : first.endpoint = second.endpoint) :
    tree graph root ≃g tree graph root :=
  (rerootIso graph root first).symm.trans <|
    (castRootIso graph sameEndpoint).trans (rerootIso graph root second)

/-- The deck transformation carrying one lift to another lift in the same
fiber. -/
noncomputable def between
    (first second : UniversalVertex graph root)
    (sameEndpoint : first.endpoint = second.endpoint) :
    DeckTransformation graph root := by
  let isomorphism := betweenIso (graph := graph) (root := root)
    first second sameEndpoint
  refine ⟨isomorphism.toEquiv, ?_, ?_⟩
  · intro point
    change (isomorphism point).endpoint = point.endpoint
    simp only [isomorphism, betweenIso, RelIso.trans_apply,
      rerootIso_symm_apply, castRootIso_apply, rerootIso_apply]
    rw [rerootMap_endpoint, castRoot_endpoint, inverseRerootMap_endpoint]
  · intro point neighbor
    exact isomorphism.map_adj_iff

/-- The constructed deck transformation has the prescribed value. -/
theorem between_apply_first
    (first second : UniversalVertex graph root)
    (sameEndpoint : first.endpoint = second.endpoint) :
    (between (graph := graph) (root := root) first second sameEndpoint).1 first =
      second := by
  unfold between
  change (betweenIso (graph := graph) (root := root)
    first second sameEndpoint) first = second
  simp only [betweenIso, RelIso.trans_apply, rerootIso_symm_apply,
    castRootIso_apply, rerootIso_apply]
  rw [inverseRerootMap_self, castRoot_base, rerootMap_base]

/-- The deck group is transitive on every nonempty endpoint fiber. -/
theorem exists_apply_eq_of_endpoint_eq
    (first second : UniversalVertex graph root)
    (sameEndpoint : first.endpoint = second.endpoint) :
    ∃ transformation : DeckTransformation graph root,
      transformation.1 first = second :=
  ⟨between (graph := graph) (root := root) first second sameEndpoint,
    between_apply_first (graph := graph) (root := root)
      first second sameEndpoint⟩

/-- A fiber of the endpoint projection. -/
abbrev EndpointFiber (vertex : Vertex) :=
  {point : UniversalVertex graph root // point.endpoint = vertex}

instance endpointFiberMulAction (vertex : Vertex) :
    MulAction (DeckTransformation graph root)
      (EndpointFiber (graph := graph) (root := root) vertex) where
  smul transformation point :=
    ⟨transformation.1 point.1,
      (endpoint_apply transformation point.1).trans point.2⟩
  one_smul point := by
    apply Subtype.ext
    rfl
  mul_smul first second point := by
    apply Subtype.ext
    rfl

/-- The tautological action of the deck group on the complete universal tree
is faithful. -/
theorem faithful_action :
    FaithfulSMul (DeckTransformation graph root)
      (UniversalVertex graph root) :=
  inferInstance

/-- Every nonempty endpoint fiber is a transitive deck-group set. -/
instance endpointFiber_isPretransitive (vertex : Vertex) :
    MulAction.IsPretransitive (DeckTransformation graph root)
      (EndpointFiber (graph := graph) (root := root) vertex) :=
  ⟨by
    intro first second
    obtain ⟨transformation, equality⟩ :=
      exists_apply_eq_of_endpoint_eq first.1 second.1
        (first.2.trans second.2.symm)
    refine ⟨transformation, ?_⟩
    apply Subtype.ext
    exact equality⟩

/-- A deck transformation is determined by the image of any one universal
vertex. -/
theorem eq_of_apply_eq (first second : DeckTransformation graph root)
    (point : UniversalVertex graph root)
    (atPoint : first.1 point = second.1 point) : first = second := by
  apply Subtype.ext
  apply Equiv.ext
  intro target
  obtain ⟨walk⟩ := (tree_connected graph root) point target
  have alongWalk : ∀ {source destination}
      (path : (tree graph root).Walk source destination),
      first.1 source = second.1 source →
        first.1 destination = second.1 destination := by
    intro source destination path
    induction path with
    | nil => exact id
    | @cons source neighbor destination adjacent tail inductionHypothesis =>
        intro atSource
        have firstAdjacent :
            (tree graph root).Adj (first.1 source) (first.1 neighbor) :=
          (adjacency_apply_iff first source neighbor).mpr adjacent
        have secondAdjacent :
            (tree graph root).Adj (first.1 source) (second.1 neighbor) := by
          rw [atSource]
          exact (adjacency_apply_iff second source neighbor).mpr adjacent
        have neighborEndpoint :
            (first.1 neighbor).endpoint = (second.1 neighbor).endpoint := by simp
        exact inductionHypothesis
          (neighbor_eq_of_endpoint_eq graph root firstAdjacent secondAdjacent
            neighborEndpoint)
  exact alongWalk walk atPoint

/-- Evaluation at one point embeds the deck group into the countable
universal tree. -/
theorem apply_injective (point : UniversalVertex graph root) :
    Function.Injective
      (fun transformation : DeckTransformation graph root =>
        transformation.1 point) := by
  intro first second equality
  exact eq_of_apply_eq first second point equality

noncomputable instance [Countable Vertex] :
    Countable (DeckTransformation graph root) :=
  Function.Injective.countable (apply_injective (base graph root))

instance : TopologicalSpace (DeckTransformation graph root) := ⊥

instance : DiscreteTopology (DeckTransformation graph root) :=
  discreteTopology_bot _

end DeckTransformation

/-- Automorphisms of a base simple graph, represented as a subgroup of its
permutation group. -/
def graphAutomorphismSubgroup : Subgroup (Equiv.Perm Vertex) where
  carrier := {automorphism | ∀ first second,
    graph.Adj (automorphism first) (automorphism second) ↔
      graph.Adj first second}
  one_mem' := by simp
  mul_mem' := by
    intro first second firstLaw secondLaw point neighbor
    exact (firstLaw (second point) (second neighbor)).trans
      (secondLaw point neighbor)
  inv_mem' := by
    intro automorphism law point neighbor
    have := law (automorphism⁻¹ point) (automorphism⁻¹ neighbor)
    simpa using this.symm

/-- A graph automorphism as an actual graph isomorphism. -/
def graphAutomorphismIso
    (automorphism : graphAutomorphismSubgroup graph) : graph ≃g graph where
  toEquiv := automorphism.1
  map_rel_iff' := by
    intro first second
    exact automorphism.2 first second

/-- A coherent semi-graph action acts on the faithful incidence graph by a
group homomorphism into its graph-automorphism group. -/
def incidenceAutomorphismHom
    {semiGraph : SourceSemiGraph.{u}} {Acting : Type u} [Group Acting]
    (action : semiGraph.Action Acting) :
    Acting →* graphAutomorphismSubgroup
      (IncidenceNode.incidenceGraph semiGraph) where
  toFun g := ⟨IncidenceNode.incidencePerm semiGraph action g,
    fun first second =>
      (IncidenceNode.incidenceIso semiGraph action g).map_rel_iff⟩
  map_one' := by
    apply Subtype.ext
    exact IncidenceNode.incidencePerm_one semiGraph action
  map_mul' first second := by
    apply Subtype.ext
    exact IncidenceNode.incidencePerm_mul semiGraph action first second

variable (symmetries : Subgroup (graphAutomorphismSubgroup graph))

/-- Deck transformations of the universal tree lying over a specified group
of base-graph symmetries.  The witnessing base symmetry is existential, so
the resulting group is literally a subgroup of tree permutations and its
action is faithful without a redundant coordinate. -/
def liftedDeckTransformationSubgroup : Subgroup
    (Equiv.Perm (UniversalVertex graph root)) where
  carrier := {transformation |
    (∃ symmetry : symmetries, ∀ point,
      (transformation point).endpoint =
        symmetry.1.1 point.endpoint) ∧
      ∀ first second,
        (tree graph root).Adj (transformation first) (transformation second) ↔
          (tree graph root).Adj first second}
  one_mem' := by
    constructor
    · refine ⟨1, ?_⟩
      intro point
      rfl
    · simp
  mul_mem' := by
    rintro first second ⟨⟨firstSymmetry, firstEndpoint⟩, firstAdjacent⟩
      ⟨⟨secondSymmetry, secondEndpoint⟩, secondAdjacent⟩
    constructor
    · refine ⟨firstSymmetry * secondSymmetry, ?_⟩
      intro point
      exact (firstEndpoint (second point)).trans <| congrArg firstSymmetry.1.1
        (secondEndpoint point)
    · intro point neighbor
      exact (firstAdjacent (second point) (second neighbor)).trans
        (secondAdjacent point neighbor)
  inv_mem' := by
    rintro transformation ⟨⟨symmetry, endpointLaw⟩, adjacencyLaw⟩
    constructor
    · refine ⟨symmetry⁻¹, ?_⟩
      intro point
      have mapped := endpointLaw (transformation⁻¹ point)
      calc
        (transformation⁻¹ point).endpoint =
            symmetry.1.1.symm
              (symmetry.1.1 (transformation⁻¹ point).endpoint) :=
          (symmetry.1.1.symm_apply_apply _).symm
        _ = symmetry.1.1.symm point.endpoint := by
          apply congrArg symmetry.1.1.symm
          simpa using mapped.symm
    · intro point neighbor
      have := adjacencyLaw (transformation⁻¹ point)
        (transformation⁻¹ neighbor)
      simpa using this.symm

/-- The group of lifts of the selected base symmetries. -/
abbrev LiftedDeckTransformation :=
  liftedDeckTransformationSubgroup graph root symmetries

namespace LiftedDeckTransformation

variable {graph root symmetries}

@[simp]
theorem adjacency_apply_iff
    (transformation : LiftedDeckTransformation graph root symmetries)
    (first second : UniversalVertex graph root) :
    (tree graph root).Adj (transformation.1 first) (transformation.1 second) ↔
      (tree graph root).Adj first second :=
  transformation.2.2 first second

/-- A chosen base symmetry witnessed by a lifted deck transformation. -/
noncomputable def baseSymmetry
    (transformation : LiftedDeckTransformation graph root symmetries) :
    symmetries :=
  Classical.choose transformation.2.1

@[simp]
theorem endpoint_apply
    (transformation : LiftedDeckTransformation graph root symmetries)
    (point : UniversalVertex graph root) :
    (transformation.1 point).endpoint =
      (baseSymmetry transformation).1.1 point.endpoint :=
  Classical.choose_spec transformation.2.1 point

/-- A lift of a base symmetry carrying `first` to `second`. -/
noncomputable def betweenIso
    (symmetry : symmetries) (first second : UniversalVertex graph root)
    (sameEndpoint :
      symmetry.1.1 first.endpoint = second.endpoint) :
    tree graph root ≃g tree graph root :=
  let baseIso := graphAutomorphismIso graph symmetry.1
  let mappedFirst := UniversalVertex.mapIso graph root baseIso first
  (UniversalVertex.universalMapIso graph root baseIso).trans <|
    (UniversalVertex.rerootIso graph (baseIso root) mappedFirst).symm.trans <|
      (UniversalVertex.castRootIso graph (by
        rw [UniversalVertex.mapIso_endpoint]
        exact sameEndpoint)).trans <|
        UniversalVertex.rerootIso graph root second

/-- The preceding isomorphism is a lifted deck transformation. -/
noncomputable def between
    (symmetry : symmetries) (first second : UniversalVertex graph root)
    (sameEndpoint : symmetry.1.1 first.endpoint = second.endpoint) :
    LiftedDeckTransformation graph root symmetries := by
  let isomorphism := betweenIso symmetry first second sameEndpoint
  refine ⟨isomorphism.toEquiv, ?_, ?_⟩
  · refine ⟨symmetry, ?_⟩
    intro point
    let baseIso := graphAutomorphismIso graph symmetry.1
    let mappedFirst := UniversalVertex.mapIso graph root baseIso first
    change (isomorphism point).endpoint = symmetry.1.1 point.endpoint
    simp only [isomorphism, betweenIso, RelIso.trans_apply,
      UniversalVertex.universalMapIso_apply,
      UniversalVertex.rerootIso_symm_apply,
      UniversalVertex.castRootIso_apply,
      UniversalVertex.rerootIso_apply]
    rw [UniversalVertex.rerootMap_endpoint,
      UniversalVertex.castRoot_endpoint,
      UniversalVertex.inverseRerootMap_endpoint,
      UniversalVertex.mapIso_endpoint]
    rfl
  · intro point neighbor
    exact isomorphism.map_adj_iff

@[simp]
theorem between_endpoint_apply
    (symmetry : symmetries) (first second : UniversalVertex graph root)
    (sameEndpoint : symmetry.1.1 first.endpoint = second.endpoint)
    (point : UniversalVertex graph root) :
    ((between symmetry first second sameEndpoint).1 point).endpoint =
      symmetry.1.1 point.endpoint := by
  unfold between
  change ((betweenIso symmetry first second sameEndpoint) point).endpoint = _
  let baseIso := graphAutomorphismIso graph symmetry.1
  let mappedFirst := UniversalVertex.mapIso graph root baseIso first
  simp only [betweenIso, RelIso.trans_apply,
    UniversalVertex.universalMapIso_apply,
    UniversalVertex.rerootIso_symm_apply,
    UniversalVertex.castRootIso_apply,
    UniversalVertex.rerootIso_apply]
  rw [UniversalVertex.rerootMap_endpoint,
    UniversalVertex.castRoot_endpoint,
    UniversalVertex.inverseRerootMap_endpoint,
    UniversalVertex.mapIso_endpoint]
  rfl

/-- The constructed lift has the prescribed value. -/
theorem between_apply_first
    (symmetry : symmetries) (first second : UniversalVertex graph root)
    (sameEndpoint : symmetry.1.1 first.endpoint = second.endpoint) :
    (between symmetry first second sameEndpoint).1 first = second := by
  unfold between
  change (betweenIso symmetry first second sameEndpoint) first = second
  let baseIso := graphAutomorphismIso graph symmetry.1
  let mappedFirst := UniversalVertex.mapIso graph root baseIso first
  simp only [betweenIso, RelIso.trans_apply,
    UniversalVertex.universalMapIso_apply,
    UniversalVertex.rerootIso_symm_apply,
    UniversalVertex.castRootIso_apply,
    UniversalVertex.rerootIso_apply]
  rw [UniversalVertex.inverseRerootMap_self,
    UniversalVertex.castRoot_base,
    UniversalVertex.rerootMap_base]

/-- Lifted deck transformations act transitively over every orbit of the
selected base-symmetry group. -/
theorem exists_apply_eq
    (first second : UniversalVertex graph root)
    (sameOrbit : ∃ symmetry : symmetries,
      symmetry.1.1 first.endpoint = second.endpoint) :
    ∃ transformation : LiftedDeckTransformation graph root symmetries,
      transformation.1 first = second := by
  obtain ⟨symmetry, sameEndpoint⟩ := sameOrbit
  exact ⟨between symmetry first second sameEndpoint,
    between_apply_first symmetry first second sameEndpoint⟩

/-- A lifted transformation is determined by its chosen base symmetry and
the image of one universal vertex. -/
theorem encoding_injective (point : UniversalVertex graph root) :
    Function.Injective (fun transformation :
      LiftedDeckTransformation graph root symmetries =>
        (baseSymmetry transformation, transformation.1 point)) := by
  intro first second equality
  have symmetryEquality := congrArg Prod.fst equality
  have symmetryEquality' : baseSymmetry first = baseSymmetry second := by
    exact symmetryEquality
  have atPoint := congrArg Prod.snd equality
  apply Subtype.ext
  apply Equiv.ext
  intro target
  obtain ⟨walk⟩ := (UniversalVertex.tree_connected graph root) point target
  have alongWalk : ∀ {source destination}
      (path : (UniversalVertex.tree graph root).Walk source destination),
      first.1 source = second.1 source →
        first.1 destination = second.1 destination := by
    intro source destination path
    induction path with
    | nil => exact id
    | @cons source neighbor destination adjacent tail inductionHypothesis =>
        intro atSource
        have firstAdjacent :
            (UniversalVertex.tree graph root).Adj
              (first.1 source) (first.1 neighbor) :=
          (adjacency_apply_iff first source neighbor).mpr adjacent
        have secondAdjacent :
            (UniversalVertex.tree graph root).Adj
              (first.1 source) (second.1 neighbor) := by
          rw [atSource]
          exact (adjacency_apply_iff second source neighbor).mpr adjacent
        have endpointEquality :
            (first.1 neighbor).endpoint = (second.1 neighbor).endpoint := by
          rw [endpoint_apply, endpoint_apply, symmetryEquality']
        exact inductionHypothesis <|
          UniversalVertex.neighbor_eq_of_endpoint_eq graph root
            firstAdjacent secondAdjacent endpointEquality
  exact alongWalk walk atPoint

/-- Two lifted deck transformations coincide when they induce the same
endpoint map and agree at one point.  This form avoids dependence on the
noncomputable choice of a witnessing base symmetry. -/
theorem eq_of_apply_eq_of_endpoint_eq
    (first second : LiftedDeckTransformation graph root symmetries)
    (endpointEquality : ∀ point,
      (first.1 point).endpoint = (second.1 point).endpoint)
    (point : UniversalVertex graph root)
    (atPoint : first.1 point = second.1 point) : first = second := by
  apply Subtype.ext
  apply Equiv.ext
  have mapEquality := UniversalVertex.map_eq_of_endpoint_eq_adj
    graph root graph root first.1 second.1 endpointEquality
    (fun {_ _} adjacent => (adjacency_apply_iff first _ _).mpr adjacent)
    (fun {_ _} adjacent => (adjacency_apply_iff second _ _).mpr adjacent)
    point atPoint
  exact congrFun mapEquality

noncomputable instance [Countable Vertex] [Countable symmetries] :
    Countable (LiftedDeckTransformation graph root symmetries) :=
  Function.Injective.countable (encoding_injective (UniversalVertex.base graph root))

instance : TopologicalSpace
    (LiftedDeckTransformation graph root symmetries) := ⊥

instance : DiscreteTopology
    (LiftedDeckTransformation graph root symmetries) :=
  discreteTopology_bot _

/-- The tautological lifted-deck action on the universal tree is faithful. -/
theorem faithful_action :
    FaithfulSMul (LiftedDeckTransformation graph root symmetries)
      (UniversalVertex graph root) :=
  inferInstance

end LiftedDeckTransformation

/-! ## Composite deck groups retaining invisible finite-level symmetry -/

variable {Acting : Type u} [Group Acting]
    (actionHom : Acting →* graphAutomorphismSubgroup graph)

/-- Pairs consisting of a finite-level symmetry and a lift of its incidence
action to the universal tree.  The symmetry coordinate is intentionally
retained: an automorphism of an anabelioid level can act trivially on its
underlying incidence graph while acting nontrivially on constituent fibers. -/
def compositeDeckTransformationSubgroup : Subgroup
    (Acting × Equiv.Perm (UniversalVertex graph root)) where
  carrier := {transformation |
    (∀ point, (transformation.2 point).endpoint =
      (actionHom transformation.1).1 point.endpoint) ∧
    ∀ first second,
      (tree graph root).Adj (transformation.2 first)
          (transformation.2 second) ↔
        (tree graph root).Adj first second}
  one_mem' := by
    constructor
    · intro point
      change point.endpoint = (actionHom 1).1 point.endpoint
      rw [map_one]
      rfl
    · simp
  mul_mem' := by
    rintro first second ⟨firstEndpoint, firstAdjacent⟩
      ⟨secondEndpoint, secondAdjacent⟩
    constructor
    · intro point
      change (first.2 (second.2 point)).endpoint = _
      rw [firstEndpoint, secondEndpoint]
      change (actionHom first.1).1 ((actionHom second.1).1 point.endpoint) =
        (actionHom (first.1 * second.1)).1 point.endpoint
      rw [map_mul]
      rfl
    · intro point neighbor
      exact (firstAdjacent (second.2 point) (second.2 neighbor)).trans
        (secondAdjacent point neighbor)
  inv_mem' := by
    rintro transformation ⟨endpointLaw, adjacencyLaw⟩
    constructor
    · intro point
      have mapped := endpointLaw (transformation.2⁻¹ point)
      calc
        (transformation.2⁻¹ point).endpoint =
            ((actionHom transformation.1).1).symm
              ((actionHom transformation.1).1
                (transformation.2⁻¹ point).endpoint) :=
          (((actionHom transformation.1).1).symm_apply_apply _).symm
        _ = ((actionHom transformation.1).1).symm point.endpoint := by
          apply congrArg ((actionHom transformation.1).1).symm
          simpa using mapped.symm
        _ = (actionHom transformation.1⁻¹).1 point.endpoint := by
          rw [map_inv]
          rfl
    · intro point neighbor
      have := adjacencyLaw (transformation.2⁻¹ point)
        (transformation.2⁻¹ neighbor)
      simpa using this.symm

/-- The complete composite deck group, including finite symmetries invisible
on the incidence graph. -/
abbrev CompositeDeckTransformation :=
  compositeDeckTransformationSubgroup graph root actionHom

namespace CompositeDeckTransformation

variable {graph root actionHom}

/-- The retained finite-level symmetry. -/
abbrev baseSymmetry
    (transformation : CompositeDeckTransformation graph root actionHom) :
    Acting :=
  transformation.1.1

/-- The lifted permutation of the universal incidence tree. -/
abbrev treePerm
    (transformation : CompositeDeckTransformation graph root actionHom) :
    Equiv.Perm (UniversalVertex graph root) :=
  transformation.1.2

@[simp]
theorem endpoint_apply
    (transformation : CompositeDeckTransformation graph root actionHom)
    (point : UniversalVertex graph root) :
    ((treePerm transformation) point).endpoint =
      (actionHom (baseSymmetry transformation)).1 point.endpoint :=
  transformation.2.1 point

@[simp]
theorem adjacency_apply_iff
    (transformation : CompositeDeckTransformation graph root actionHom)
    (first second : UniversalVertex graph root) :
    (tree graph root).Adj ((treePerm transformation) first)
        ((treePerm transformation) second) ↔
      (tree graph root).Adj first second :=
  transformation.2.2 first second

/-- A finite-level symmetry with prescribed endpoint displacement has a
canonical lift carrying one selected universal vertex to another. -/
noncomputable def between
    (symmetry : Acting) (first second : UniversalVertex graph root)
    (sameEndpoint :
      (actionHom symmetry).1 first.endpoint = second.endpoint) :
    CompositeDeckTransformation graph root actionHom := by
  let visible : actionHom.range :=
    ⟨actionHom symmetry, ⟨symmetry, rfl⟩⟩
  let lifted := LiftedDeckTransformation.between
    visible first second sameEndpoint
  refine ⟨⟨symmetry, lifted.1⟩, ?_, lifted.2.2⟩
  intro point
  exact LiftedDeckTransformation.between_endpoint_apply
    visible first second sameEndpoint point

@[simp]
theorem between_apply_first
    (symmetry : Acting) (first second : UniversalVertex graph root)
    (sameEndpoint :
      (actionHom symmetry).1 first.endpoint = second.endpoint) :
    (treePerm (between symmetry first second sameEndpoint)) first = second := by
  let visible : actionHom.range :=
    ⟨actionHom symmetry, ⟨symmetry, rfl⟩⟩
  have visibleEndpoint : visible.1.1 first.endpoint = second.endpoint :=
    sameEndpoint
  change (LiftedDeckTransformation.between visible first second
    visibleEndpoint).1 first = second
  exact LiftedDeckTransformation.between_apply_first
    visible first second visibleEndpoint

/-- The complete composite group is transitive whenever the retained finite
symmetry group is transitive on the relevant endpoints. -/
theorem exists_treePerm_eq
    (first second : UniversalVertex graph root)
    (sameOrbit : ∃ symmetry : Acting,
      (actionHom symmetry).1 first.endpoint = second.endpoint) :
    ∃ transformation : CompositeDeckTransformation graph root actionHom,
      (treePerm transformation) first = second := by
  obtain ⟨symmetry, endpointEquality⟩ := sameOrbit
  exact ⟨between symmetry first second endpointEquality,
    between_apply_first symmetry first second endpointEquality⟩

/-- A composite transformation is determined by its retained finite
symmetry and the image of one universal vertex. -/
theorem encoding_injective (point : UniversalVertex graph root) :
    Function.Injective (fun transformation :
      CompositeDeckTransformation graph root actionHom ↦
        (baseSymmetry transformation, (treePerm transformation) point)) := by
  intro first second equality
  have symmetryEquality : baseSymmetry first = baseSymmetry second :=
    congrArg (fun value : Acting × UniversalVertex graph root => value.1)
      equality
  have atPoint : (treePerm first) point = (treePerm second) point :=
    congrArg (fun value : Acting × UniversalVertex graph root => value.2)
      equality
  apply Subtype.ext
  apply Prod.ext symmetryEquality
  apply Equiv.ext
  have endpointEquality : ∀ target,
      ((treePerm first) target).endpoint =
        ((treePerm second) target).endpoint := by
    intro target
    rw [endpoint_apply, endpoint_apply, symmetryEquality]
  have mapEquality := UniversalVertex.map_eq_of_endpoint_eq_adj
    graph root graph root (treePerm first) (treePerm second) endpointEquality
    (fun {_ _} adjacent ↦
      (adjacency_apply_iff first _ _).mpr adjacent)
    (fun {_ _} adjacent ↦
      (adjacency_apply_iff second _ _).mpr adjacent)
    point atPoint
  exact congrFun mapEquality

/-- A nontrivial composite transformation with trivial retained finite
symmetry must move the distinguished vertex of the universal incidence tree. -/
theorem treePerm_base_ne_base_of_ne_one
    (transformation : CompositeDeckTransformation graph root actionHom)
    (symmetryEqualsOne : baseSymmetry transformation = 1)
    (transformationNontrivial : transformation ≠ 1) :
    treePerm transformation (UniversalVertex.base graph root) ≠
      UniversalVertex.base graph root := by
  intro fixesBase
  apply transformationNontrivial
  apply encoding_injective (UniversalVertex.base graph root)
  apply Prod.ext
  · change baseSymmetry transformation = (1 : Acting)
    exact symmetryEqualsOne
  · exact fixesBase

/-- Consequently the reduced loop encoded by the transformed base vertex has
positive length. -/
theorem treePerm_base_depth_ne_zero_of_ne_one
    (transformation : CompositeDeckTransformation graph root actionHom)
    (symmetryEqualsOne : baseSymmetry transformation = 1)
    (transformationNontrivial : transformation ≠ 1) :
    (treePerm transformation (UniversalVertex.base graph root)).depth ≠ 0 := by
  intro depthEqualsZero
  exact treePerm_base_ne_base_of_ne_one transformation symmetryEqualsOne
    transformationNontrivial
      (UniversalVertex.eq_base_of_depth_eq_zero graph root _ depthEqualsZero)

noncomputable instance [Countable Vertex] [Countable Acting] :
    Countable (CompositeDeckTransformation graph root actionHom) :=
  Function.Injective.countable
    (encoding_injective (UniversalVertex.base graph root))

instance : TopologicalSpace
    (CompositeDeckTransformation graph root actionHom) := ⊥

instance : DiscreteTopology
    (CompositeDeckTransformation graph root actionHom) :=
  discreteTopology_bot _

/-- The visible action of a composite transformation on the universal tree. -/
instance treeMulAction :
    MulAction (CompositeDeckTransformation graph root actionHom)
      (UniversalVertex graph root) where
  smul transformation point := (treePerm transformation) point
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

variable (Fiber : Type u) [MulAction Acting Fiber]

/-- A faithful realization couples the universal incidence tree with a
constituent fiber on which the retained finite Galois symmetry acts. -/
instance constituentFiberMulAction :
    MulAction (CompositeDeckTransformation graph root actionHom)
      (UniversalVertex graph root × Fiber) where
  smul transformation point :=
    ((treePerm transformation) point.1,
      baseSymmetry transformation • point.2)
  one_smul point := by
    apply Prod.ext
    · rfl
    · exact one_smul Acting point.2
  mul_smul first second point := by
    apply Prod.ext
    · rfl
    · exact mul_smul (baseSymmetry first) (baseSymmetry second) point.2

/-- Coupling with a faithful constituent action makes the complete deck
action faithful without quotienting away incidence-invisible symmetries. -/
theorem constituentFiber_faithful [FaithfulSMul Acting Fiber]
    [Nonempty (UniversalVertex graph root)] [Nonempty Fiber] :
    FaithfulSMul (CompositeDeckTransformation graph root actionHom)
      (UniversalVertex graph root × Fiber) where
  eq_of_smul_eq_smul := by
    intro first second actionEquality
    obtain ⟨treePoint⟩ :=
      (inferInstance : Nonempty (UniversalVertex graph root))
    obtain ⟨fiberPoint⟩ := (inferInstance : Nonempty Fiber)
    have symmetryEquality : baseSymmetry first = baseSymmetry second := by
      apply FaithfulSMul.eq_of_smul_eq_smul (M := Acting) (α := Fiber)
      intro point
      exact congrArg Prod.snd (actionEquality (treePoint, point))
    have treeEquality : treePerm first = treePerm second := by
      apply Equiv.ext
      intro point
      exact congrArg Prod.fst (actionEquality (point, fiberPoint))
    apply Subtype.ext
    exact Prod.ext symmetryEquality treeEquality

end CompositeDeckTransformation

end UniversalVertex

namespace IncidenceNode

variable {semiGraph target : SourceSemiGraph.{u}}

/-- A graph-covering of source semi-graphs is locally injective on the faithful
incidence graphs. -/
theorem properIncidenceGraphHom_isLocallyInjective
    (hom : semiGraph.Hom target) (covering : hom.IsGraphCovering) :
    UniversalVertex.IsLocallyInjective (incidenceGraph semiGraph)
      (incidenceGraph target)
      (properIncidenceGraphHom semiGraph hom covering.1) := by
  intro center first second firstAdjacent secondAdjacent mappedEquality
  cases center with
  | vertex center =>
      cases first with
      | vertex firstVertex =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at firstAdjacent
      | edge firstEdge =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at firstAdjacent
      | branch firstBranch =>
          cases second with
          | vertex secondVertex =>
              simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
                at secondAdjacent
          | edge secondEdge =>
              simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
                at secondAdjacent
          | branch secondBranch =>
              have firstCoincidence :=
                (vertex_branch_adj semiGraph center firstBranch).mp firstAdjacent
              have secondCoincidence :=
                (vertex_branch_adj semiGraph center secondBranch).mp secondAdjacent
              have mappedBranchEquality :
                  hom.totalBranchMap firstBranch =
                    hom.totalBranchMap secondBranch := by
                exact IncidenceNode.branch.inj mappedEquality
              cases center with
              | inl vertex =>
                  let firstIncident : semiGraph.IncidentBranch vertex :=
                    ⟨firstBranch,
                      coincidence_eq_of_compactification_original
                        semiGraph firstBranch vertex firstCoincidence⟩
                  let secondIncident : semiGraph.IncidentBranch vertex :=
                    ⟨secondBranch,
                      coincidence_eq_of_compactification_original
                        semiGraph secondBranch vertex secondCoincidence⟩
                  have mappedIncidentEquality :
                      hom.incidentBranchMap vertex firstIncident =
                        hom.incidentBranchMap vertex secondIncident := by
                    apply Subtype.ext
                    exact mappedBranchEquality
                  have incidentEquality :=
                    covering.2 vertex |>.1 mappedIncidentEquality
                  exact congrArg (fun incident => IncidenceNode.branch incident.1) 
                    incidentEquality
              | inr boundary =>
                  have firstEquality :=
                    totalBranch_eq_of_compactification_boundary
                      semiGraph firstBranch boundary firstCoincidence
                  have secondEquality :=
                    totalBranch_eq_of_compactification_boundary
                      semiGraph secondBranch boundary secondCoincidence
                  exact congrArg IncidenceNode.branch
                    (firstEquality.trans secondEquality.symm)
  | edge centerEdge =>
      cases first with
      | vertex firstVertex =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at firstAdjacent
      | edge firstEdge =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at firstAdjacent
      | branch firstBranch =>
          cases second with
          | vertex secondVertex =>
              simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
                at secondAdjacent
          | edge secondEdge =>
              simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
                at secondAdjacent
          | branch secondBranch =>
              have firstSupport :=
                (edge_branch_adj semiGraph centerEdge firstBranch).mp firstAdjacent
              have secondSupport :=
                (edge_branch_adj semiGraph centerEdge secondBranch).mp secondAdjacent
              rcases firstBranch with ⟨firstEdge, firstBranch⟩
              rcases secondBranch with ⟨secondEdge, secondBranch⟩
              change firstEdge = centerEdge at firstSupport
              change secondEdge = centerEdge at secondSupport
              subst firstEdge
              subst secondEdge
              have mappedBranchEquality :
                  hom.totalBranchMap
                      (⟨centerEdge, firstBranch⟩ : semiGraph.TotalBranch) =
                    hom.totalBranchMap
                      (⟨centerEdge, secondBranch⟩ : semiGraph.TotalBranch) := by
                exact IncidenceNode.branch.inj mappedEquality
              have branchEquality : firstBranch = secondBranch := by
                apply (hom.branchEquiv centerEdge).injective
                exact eq_of_heq (Sigma.mk.inj_iff.mp mappedBranchEquality).2
              subst secondBranch
              rfl
  | branch centerBranch =>
      cases first with
      | vertex firstVertex =>
          cases second with
          | vertex secondVertex =>
              have firstEndpoint :=
                (branch_vertex_adj semiGraph centerBranch firstVertex).mp
                  firstAdjacent
              have secondEndpoint :=
                (branch_vertex_adj semiGraph centerBranch secondVertex).mp
                  secondAdjacent
              exact congrArg IncidenceNode.vertex <|
                Option.some.inj (firstEndpoint.symm.trans secondEndpoint)
          | edge secondEdge => cases mappedEquality
          | branch secondBranch =>
              simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
                at secondAdjacent
      | edge firstEdge =>
          cases second with
          | vertex secondVertex => cases mappedEquality
          | edge secondEdge =>
              have firstSupport :=
                (branch_edge_adj semiGraph centerBranch firstEdge).mp firstAdjacent
              have secondSupport :=
                (branch_edge_adj semiGraph centerBranch secondEdge).mp secondAdjacent
              exact congrArg IncidenceNode.edge
                (firstSupport.symm.trans secondSupport)
          | branch secondBranch =>
              simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
                at secondAdjacent
      | branch firstBranch =>
          simp [incidenceGraph, incidenceRel, SimpleGraph.fromRel_adj]
            at firstAdjacent

end IncidenceNode

/-- A proper semi-graph morphism that is bijective on vertices and edges
reflects source-faithful connectedness from its target.  The branch
equivalences built into a morphism supply the remaining inverse data. -/
theorem source_isConnected_of_bijective_hom
    (source target : SourceSemiGraph.{u}) (hom : source.Hom target)
    (proper : hom.IsProper)
    (vertexBijective : Function.Bijective hom.vertexMap)
    (edgeBijective : Function.Bijective hom.edgeMap)
    (targetConnected : target.IsConnected) :
    source.IsConnected := by
  let vertexEquiv : source.Vertex ≃ target.Vertex :=
    Equiv.ofBijective hom.vertexMap vertexBijective
  let edgeEquiv : source.Edge ≃ target.Edge :=
    Equiv.ofBijective hom.edgeMap edgeBijective
  have reflectsAdjacent (first second : target.Vertex)
      (adjacent : target.Adjacent first second) :
      source.Adjacent (vertexEquiv.symm first) (vertexEquiv.symm second) := by
    rcases adjacent with ⟨targetEdge, firstBranch, secondBranch,
      branchesDistinct, firstCoincidence, secondCoincidence⟩
    obtain ⟨sourceEdge, edgeEquality⟩ := edgeBijective.2 targetEdge
    revert secondCoincidence firstCoincidence branchesDistinct
      secondBranch firstBranch
    subst targetEdge
    intro firstBranch secondBranch branchesDistinct
      firstCoincidence secondCoincidence
    change target.coincidence (hom.edgeMap sourceEdge) firstBranch =
      some first at firstCoincidence
    change target.coincidence (hom.edgeMap sourceEdge) secondBranch =
      some second at secondCoincidence
    let sourceFirst := (hom.branchEquiv sourceEdge).symm firstBranch
    let sourceSecond := (hom.branchEquiv sourceEdge).symm secondBranch
    have sourceBranchesDistinct : sourceFirst ≠ sourceSecond := by
      intro equality
      apply branchesDistinct
      calc
        firstBranch = hom.branchEquiv sourceEdge sourceFirst :=
          (hom.branchEquiv sourceEdge).apply_symm_apply firstBranch |>.symm
        _ = hom.branchEquiv sourceEdge sourceSecond :=
          congrArg (hom.branchEquiv sourceEdge) equality
        _ = secondBranch :=
          (hom.branchEquiv sourceEdge).apply_symm_apply secondBranch
    obtain ⟨actualFirst, actualFirstCoincidence⟩ :=
      (proper sourceEdge sourceFirst).mpr ⟨first, by
        simpa [sourceFirst] using firstCoincidence⟩
    have mappedFirstCoincidence := hom.map_coincidence sourceEdge sourceFirst
      actualFirst actualFirstCoincidence
    have mappedFirstEquality : hom.vertexMap actualFirst = first := by
      apply Option.some.inj
      exact mappedFirstCoincidence.symm.trans <| by
        simpa [sourceFirst] using firstCoincidence
    have actualFirstEquality : actualFirst = vertexEquiv.symm first := by
      apply vertexBijective.1
      rw [mappedFirstEquality]
      exact (vertexEquiv.apply_symm_apply first).symm
    subst actualFirst
    obtain ⟨actualSecond, actualSecondCoincidence⟩ :=
      (proper sourceEdge sourceSecond).mpr ⟨second, by
        simpa [sourceSecond] using secondCoincidence⟩
    have mappedSecondCoincidence := hom.map_coincidence sourceEdge sourceSecond
      actualSecond actualSecondCoincidence
    have mappedSecondEquality : hom.vertexMap actualSecond = second := by
      apply Option.some.inj
      exact mappedSecondCoincidence.symm.trans <| by
        simpa [sourceSecond] using secondCoincidence
    have actualSecondEquality : actualSecond = vertexEquiv.symm second := by
      apply vertexBijective.1
      rw [mappedSecondEquality]
      exact (vertexEquiv.apply_symm_apply second).symm
    subst actualSecond
    exact ⟨sourceEdge, sourceFirst, sourceSecond, sourceBranchesDistinct,
      actualFirstCoincidence, actualSecondCoincidence⟩
  rcases targetConnected with verticial | isolated
  · refine Or.inl ⟨⟨vertexEquiv.symm (Classical.choice verticial.1)⟩,
      ?_, ?_⟩
    · intro sourceEdge
      obtain ⟨targetVertex, targetBranch, targetCoincidence⟩ :=
        verticial.2.1 (hom.edgeMap sourceEdge)
      change target.coincidence (hom.edgeMap sourceEdge) targetBranch =
        some targetVertex at targetCoincidence
      let sourceBranch := (hom.branchEquiv sourceEdge).symm targetBranch
      obtain ⟨sourceVertex, sourceCoincidence⟩ :=
        (proper sourceEdge sourceBranch).mpr ⟨targetVertex, by
          simpa [sourceBranch] using targetCoincidence⟩
      exact ⟨sourceVertex, sourceBranch, sourceCoincidence⟩
    · intro first second
      have targetPath := verticial.2.2
        (hom.vertexMap first) (hom.vertexMap second)
      have sourcePath := targetPath.lift vertexEquiv.symm reflectsAdjacent
      convert sourcePath using 1
      · exact (vertexEquiv.symm_apply_apply first).symm
      · exact (vertexEquiv.symm_apply_apply second).symm
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · letI : IsEmpty target.Vertex := isolated.1
      exact ⟨fun vertex => isEmptyElim (hom.vertexMap vertex)⟩
    · exact ⟨edgeEquiv.symm (Classical.choice isolated.2.1)⟩
    · letI : Subsingleton target.Edge := isolated.2.2
      exact ⟨fun first second => edgeBijective.1 (Subsingleton.elim _ _)⟩

namespace SourceSemiGraphUniversalCover

variable (semiGraph : SourceSemiGraph.{u}) (root : semiGraph.Vertex)

/-- The selected root in the faithful incidence realization. -/
abbrev incidenceRoot : IncidenceNode semiGraph :=
  IncidenceNode.vertex (Sum.inl root)

/-- The universal reduced-walk tree of the compactified incidence graph. -/
abbrev IncidenceTreeVertex :=
  UniversalVertex (IncidenceNode.incidenceGraph semiGraph)
    (incidenceRoot semiGraph root)

/-- The compactified vertex at the end of a branch. -/
noncomputable def compactEndpoint (edge : semiGraph.Edge)
    (branch : semiGraph.Branch edge) : semiGraph.CompactVertex :=
  Classical.choose (semiGraph.compactification_isGraph edge branch)

@[simp]
theorem compactEndpoint_spec (edge : semiGraph.Edge)
    (branch : semiGraph.Branch edge) :
    semiGraph.compactification.coincidence edge branch =
      some (compactEndpoint semiGraph edge branch) :=
  Classical.choose_spec (semiGraph.compactification_isGraph edge branch)

theorem compactEndpoint_of_some {edge : semiGraph.Edge}
    {branch : semiGraph.Branch edge} {vertex : semiGraph.Vertex}
    (coincidence : semiGraph.coincidence edge branch = some vertex) :
    compactEndpoint semiGraph edge branch = Sum.inl vertex := by
  apply Option.some.inj
  rw [← compactEndpoint_spec]
  exact semiGraph.compactification_coincidence_of_some coincidence

/-- A lifted original vertex.  Boundary vertices of the compactification are
not included, so open branches remain open after lifting. -/
structure LiftedVertex where
  path : IncidenceTreeVertex semiGraph root
  vertex : semiGraph.Vertex
  endpoint_eq : path.endpoint = IncidenceNode.vertex (Sum.inl vertex)

/-- A lifted edge. -/
structure LiftedEdge where
  path : IncidenceTreeVertex semiGraph root
  edge : semiGraph.Edge
  endpoint_eq : path.endpoint = IncidenceNode.edge edge

namespace LiftedVertex

theorem path_injective : Function.Injective
    (path : LiftedVertex semiGraph root → IncidenceTreeVertex semiGraph root) := by
  intro first second equality
  rcases first with ⟨firstPath, firstVertex, firstEndpoint⟩
  rcases second with ⟨secondPath, secondVertex, secondEndpoint⟩
  dsimp only at equality
  subst secondPath
  have vertexEquality : firstVertex = secondVertex := by
    exact Sum.inl.inj <| IncidenceNode.vertex.inj <|
      firstEndpoint.symm.trans secondEndpoint
  subst secondVertex
  rfl

noncomputable instance [Countable semiGraph.Vertex]
    [Countable semiGraph.Edge] : Countable (LiftedVertex semiGraph root) :=
  (path_injective semiGraph root).countable

end LiftedVertex

namespace LiftedEdge

theorem path_injective : Function.Injective
    (path : LiftedEdge semiGraph root → IncidenceTreeVertex semiGraph root) := by
  intro first second equality
  rcases first with ⟨firstPath, firstEdge, firstEndpoint⟩
  rcases second with ⟨secondPath, secondEdge, secondEndpoint⟩
  dsimp only at equality
  subst secondPath
  have edgeEquality : firstEdge = secondEdge :=
    IncidenceNode.edge.inj <| firstEndpoint.symm.trans secondEndpoint
  subst secondEdge
  rfl

noncomputable instance [Countable semiGraph.Vertex]
    [Countable semiGraph.Edge] : Countable (LiftedEdge semiGraph root) :=
  (path_injective semiGraph root).countable

end LiftedEdge

/-- Lift an edge-to-branch incidence from a chosen lifted edge. -/
noncomputable def branchPath (edge : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch edge.edge) :
    IncidenceTreeVertex semiGraph root :=
  UniversalVertex.liftNeighbor _ _ edge.path
    (IncidenceNode.branch (⟨edge.edge, branch⟩ : semiGraph.TotalBranch))
    (by
      rw [edge.endpoint_eq, IncidenceNode.edge_branch_adj]
      rfl)

/-- Continue the lifted incidence path from a branch to its compactified
endpoint. -/
noncomputable def compactVertexPath (edge : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch edge.edge) :
    IncidenceTreeVertex semiGraph root :=
  UniversalVertex.liftNeighbor _ _ (branchPath semiGraph root edge branch)
    (IncidenceNode.vertex (compactEndpoint semiGraph edge.edge branch))
    (by
      rw [branchPath, UniversalVertex.liftNeighbor_endpoint,
        IncidenceNode.branch_vertex_adj]
      exact compactEndpoint_spec semiGraph edge.edge branch)

@[simp]
theorem compactVertexPath_endpoint (edge : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch edge.edge) :
    (compactVertexPath semiGraph root edge branch).endpoint =
      IncidenceNode.vertex (compactEndpoint semiGraph edge.edge branch) :=
  UniversalVertex.liftNeighbor_endpoint _ _ _ _ _

/-- Coincidence in the lifted source semi-graph. -/
noncomputable def coincidence (edge : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch edge.edge) :
    Option (LiftedVertex semiGraph root) :=
  match branchCoincidence : semiGraph.coincidence edge.edge branch with
  | none => none
  | some vertex => some
      ⟨compactVertexPath semiGraph root edge branch, vertex, by
        rw [compactVertexPath_endpoint,
          compactEndpoint_of_some semiGraph branchCoincidence]⟩

/-- Evaluation rule for lifted coincidence at a verticial source branch. -/
theorem coincidence_eq_some_of_eq_some (edge : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch edge.edge) (vertex : semiGraph.Vertex)
    (sourceCoincidence : semiGraph.coincidence edge.edge branch = some vertex) :
    coincidence semiGraph root edge branch = some
      ⟨compactVertexPath semiGraph root edge branch, vertex, by
        rw [compactVertexPath_endpoint,
          compactEndpoint_of_some semiGraph sourceCoincidence]⟩ := by
  unfold coincidence
  split
  next noCoincidence =>
    rw [sourceCoincidence] at noCoincidence
    contradiction
  next targetVertex targetCoincidence =>
    have vertexEquality : targetVertex = vertex :=
      Option.some.inj (targetCoincidence.symm.trans sourceCoincidence)
    subst targetVertex
    rfl

/-- The combinatorial universal covering semi-graph, obtained by removing the
lifts of compactification boundary vertices from the reduced-walk tree. -/
noncomputable def semiGraphCover : SourceSemiGraph.{u} where
  Vertex := LiftedVertex semiGraph root
  Edge := LiftedEdge semiGraph root
  Branch := fun edge => semiGraph.Branch edge.edge
  branchFintype := fun edge => semiGraph.branchFintype edge.edge
  branch_card := fun edge => semiGraph.branch_card edge.edge
  coincidence := coincidence semiGraph root

/-- Read every faithful-incidence node of the lifted semi-graph as the
universal-tree path that constructed it.  Original lifted vertices and edges
store this path directly; branch and compactification-boundary nodes use the
two intermediate paths of the lifted incidence. -/
noncomputable def coverIncidencePath :
    IncidenceNode (semiGraphCover semiGraph root) →
      IncidenceTreeVertex semiGraph root
  | .vertex (.inl liftedVertex) => liftedVertex.path
  | .vertex (.inr boundary) =>
      compactVertexPath semiGraph root boundary.1.1 boundary.1.2
  | .edge liftedEdge => liftedEdge.path
  | .branch liftedBranch =>
      branchPath semiGraph root liftedBranch.1 liftedBranch.2

/-- The compactified base vertex underlying a lifted compactified vertex. -/
noncomputable def coverBaseCompactVertex :
    (semiGraphCover semiGraph root).CompactVertex → semiGraph.CompactVertex
  | .inl liftedVertex => Sum.inl liftedVertex.vertex
  | .inr boundary =>
      compactEndpoint semiGraph boundary.1.1.edge boundary.1.2

@[simp]
theorem coverIncidencePath_vertex_endpoint
    (vertex : (semiGraphCover semiGraph root).CompactVertex) :
    (coverIncidencePath semiGraph root (IncidenceNode.vertex vertex)).endpoint =
      IncidenceNode.vertex (coverBaseCompactVertex semiGraph root vertex) := by
  cases vertex with
  | inl liftedVertex => exact liftedVertex.endpoint_eq
  | inr boundary => exact compactVertexPath_endpoint semiGraph root _ _

@[simp]
theorem coverIncidencePath_edge_endpoint
    (edge : LiftedEdge semiGraph root) :
    (coverIncidencePath semiGraph root (IncidenceNode.edge edge)).endpoint =
      IncidenceNode.edge edge.edge :=
  edge.endpoint_eq

@[simp]
theorem coverIncidencePath_branch_endpoint
    (branch : (semiGraphCover semiGraph root).TotalBranch) :
    (coverIncidencePath semiGraph root (IncidenceNode.branch branch)).endpoint =
      IncidenceNode.branch ⟨branch.1.edge, branch.2⟩ :=
  UniversalVertex.liftNeighbor_endpoint _ _ _ _ _

/-- A lifted incidence records exactly the path of its target vertex. -/
theorem compactVertexPath_eq_of_coincidence
    (edge : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch edge.edge)
    (vertex : LiftedVertex semiGraph root)
    (coincidence :
      (semiGraphCover semiGraph root).coincidence edge branch = some vertex) :
    compactVertexPath semiGraph root edge branch = vertex.path := by
  change SourceSemiGraphUniversalCover.coincidence semiGraph root edge branch =
    some vertex at coincidence
  unfold SourceSemiGraphUniversalCover.coincidence at coincidence
  split at coincidence
  next _ => cases coincidence
  next targetVertex targetCoincidence =>
    exact congrArg LiftedVertex.path (Option.some.inj coincidence)

/-- The preceding path map preserves faithful incidence. -/
noncomputable def coverIncidenceGraphHom :
    IncidenceNode.incidenceGraph (semiGraphCover semiGraph root) →g
      UniversalVertex.tree (IncidenceNode.incidenceGraph semiGraph)
        (incidenceRoot semiGraph root) where
  toFun := coverIncidencePath semiGraph root
  map_rel' := by
    intro first second adjacent
    cases first with
    | vertex firstVertex =>
        cases second with
        | vertex secondVertex =>
            simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
              SimpleGraph.fromRel_adj] at adjacent
        | edge secondEdge =>
            simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
              SimpleGraph.fromRel_adj] at adjacent
        | branch secondBranch =>
            have endpoint := (IncidenceNode.vertex_branch_adj
              (semiGraphCover semiGraph root) firstVertex secondBranch).mp
                adjacent
            cases firstVertex with
            | inl liftedVertex =>
                have sourceCoincidence :=
                  IncidenceNode.coincidence_eq_of_compactification_original
                    (semiGraphCover semiGraph root) secondBranch liftedVertex
                      endpoint
                have pathEquality := compactVertexPath_eq_of_coincidence
                  semiGraph root secondBranch.1 secondBranch.2 liftedVertex
                    sourceCoincidence
                rw [coverIncidencePath, coverIncidencePath, ← pathEquality]
                exact (UniversalVertex.adjacent_liftNeighbor _ _
                  (branchPath semiGraph root secondBranch.1 secondBranch.2)
                  (IncidenceNode.vertex
                    (compactEndpoint semiGraph secondBranch.1.edge
                      secondBranch.2)) _).symm
            | inr boundary =>
                have branchEquality :=
                  IncidenceNode.totalBranch_eq_of_compactification_boundary
                    (semiGraphCover semiGraph root) secondBranch boundary endpoint
                cases branchEquality
                rw [coverIncidencePath, coverIncidencePath]
                exact (UniversalVertex.adjacent_liftNeighbor _ _
                  (branchPath semiGraph root boundary.1.1 boundary.1.2)
                  (IncidenceNode.vertex
                    (compactEndpoint semiGraph boundary.1.1.edge
                      boundary.1.2)) _).symm
    | edge firstEdge =>
        cases second with
        | vertex secondVertex =>
            simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
              SimpleGraph.fromRel_adj] at adjacent
        | edge secondEdge =>
            simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
              SimpleGraph.fromRel_adj] at adjacent
        | branch secondBranch =>
            have support := (IncidenceNode.edge_branch_adj
              (semiGraphCover semiGraph root) firstEdge secondBranch).mp adjacent
            rcases secondBranch with ⟨secondEdge, secondBranch⟩
            change secondEdge = firstEdge at support
            subst secondEdge
            rw [coverIncidencePath, coverIncidencePath]
            exact UniversalVertex.adjacent_liftNeighbor _ _ firstEdge.path
              (IncidenceNode.branch
                (⟨firstEdge.edge, secondBranch⟩ : semiGraph.TotalBranch)) _
    | branch firstBranch =>
        cases second with
        | branch secondBranch =>
            simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
              SimpleGraph.fromRel_adj] at adjacent
        | edge secondEdge =>
            have support := (IncidenceNode.branch_edge_adj
              (semiGraphCover semiGraph root) firstBranch secondEdge).mp adjacent
            rcases firstBranch with ⟨firstEdge, firstBranch⟩
            change firstEdge = secondEdge at support
            subst secondEdge
            rw [coverIncidencePath, coverIncidencePath]
            exact (UniversalVertex.adjacent_liftNeighbor _ _ firstEdge.path
              (IncidenceNode.branch
                (⟨firstEdge.edge, firstBranch⟩ : semiGraph.TotalBranch)) _).symm
        | vertex secondVertex =>
            have endpoint := (IncidenceNode.branch_vertex_adj
              (semiGraphCover semiGraph root) firstBranch secondVertex).mp adjacent
            cases secondVertex with
            | inl liftedVertex =>
                have sourceCoincidence :=
                  IncidenceNode.coincidence_eq_of_compactification_original
                    (semiGraphCover semiGraph root) firstBranch liftedVertex endpoint
                have pathEquality := compactVertexPath_eq_of_coincidence
                  semiGraph root firstBranch.1 firstBranch.2 liftedVertex
                    sourceCoincidence
                rw [coverIncidencePath, coverIncidencePath, ← pathEquality]
                exact UniversalVertex.adjacent_liftNeighbor _ _
                  (branchPath semiGraph root firstBranch.1 firstBranch.2)
                  (IncidenceNode.vertex
                    (compactEndpoint semiGraph firstBranch.1.edge
                      firstBranch.2)) _
            | inr boundary =>
                have branchEquality :=
                  IncidenceNode.totalBranch_eq_of_compactification_boundary
                    (semiGraphCover semiGraph root) firstBranch boundary endpoint
                cases branchEquality
                rw [coverIncidencePath, coverIncidencePath]
                exact UniversalVertex.adjacent_liftNeighbor _ _
                  (branchPath semiGraph root boundary.1.1 boundary.1.2)
                  (IncidenceNode.vertex
                    (compactEndpoint semiGraph boundary.1.1.edge
                      boundary.1.2)) _

/-- The lifted edge adjacent to a universal-tree point whose endpoint is a
branch node. -/
noncomputable def liftedEdgeOfBranchPath
    (point : IncidenceTreeVertex semiGraph root)
    (branch : semiGraph.TotalBranch)
    (endpoint : point.endpoint = IncidenceNode.branch branch) :
    LiftedEdge semiGraph root where
  path := UniversalVertex.liftNeighbor _ _ point
    (IncidenceNode.edge branch.1) (by
      rw [endpoint, IncidenceNode.branch_edge_adj]
      rfl)
  edge := branch.1
  endpoint_eq := UniversalVertex.liftNeighbor_endpoint _ _ _ _ _

/-- The intermediate branch point adjacent to a universal-tree
compactification-boundary point. -/
noncomputable def branchPathOfBoundaryPath
    (point : IncidenceTreeVertex semiGraph root)
    (boundary : semiGraph.NonVerticialBranch)
    (endpoint : point.endpoint = IncidenceNode.vertex (Sum.inr boundary)) :
    IncidenceTreeVertex semiGraph root :=
  UniversalVertex.liftNeighbor _ _ point
    (IncidenceNode.branch boundary.1) (by
      rw [endpoint, IncidenceNode.vertex_branch_adj]
      exact semiGraph.compactification_coincidence_of_none boundary.2)

/-- The lifted edge adjacent to the branch adjacent to a universal-tree
compactification-boundary point. -/
noncomputable def liftedEdgeOfBoundaryPath
    (point : IncidenceTreeVertex semiGraph root)
    (boundary : semiGraph.NonVerticialBranch)
    (endpoint : point.endpoint = IncidenceNode.vertex (Sum.inr boundary)) :
    LiftedEdge semiGraph root where
  path := UniversalVertex.liftNeighbor _ _
    (branchPathOfBoundaryPath semiGraph root point boundary endpoint)
    (IncidenceNode.edge boundary.1.1) (by
      rw [branchPathOfBoundaryPath,
        UniversalVertex.liftNeighbor_endpoint,
        IncidenceNode.branch_edge_adj]
      rfl)
  edge := boundary.1.1
  endpoint_eq := UniversalVertex.liftNeighbor_endpoint _ _ _ _ _

/-- The nonverticial branch of the lifted edge reconstructed from a
universal-tree boundary point. -/
noncomputable def liftedBoundaryBranch
    (point : IncidenceTreeVertex semiGraph root)
    (boundary : semiGraph.NonVerticialBranch)
    (endpoint : point.endpoint = IncidenceNode.vertex (Sum.inr boundary)) :
    (semiGraphCover semiGraph root).NonVerticialBranch := by
  let liftedEdge := liftedEdgeOfBoundaryPath
    semiGraph root point boundary endpoint
  refine ⟨⟨liftedEdge, boundary.1.2⟩, ?_⟩
  change coincidence semiGraph root liftedEdge boundary.1.2 = none
  have noCoincidence :
      semiGraph.coincidence liftedEdge.edge boundary.1.2 = none := by
    change semiGraph.coincidence boundary.1.1 boundary.1.2 = none
    exact boundary.2
  unfold coincidence
  split
  next _ => rfl
  next vertex branchCoincidence =>
    rw [noCoincidence] at branchCoincidence
    cases branchCoincidence

@[simp]
theorem liftedBoundaryBranch_val
    (point : IncidenceTreeVertex semiGraph root)
    (boundary : semiGraph.NonVerticialBranch)
    (endpoint : point.endpoint = IncidenceNode.vertex (Sum.inr boundary)) :
    (liftedBoundaryBranch semiGraph root point boundary endpoint).1 =
      ⟨liftedEdgeOfBoundaryPath semiGraph root point boundary endpoint,
        boundary.1.2⟩ := by
  unfold liftedBoundaryBranch
  rfl

/-- Reconstruct the unique faithful-incidence node of the lifted semi-graph
represented by a universal-tree point. -/
noncomputable def pathIncidenceNode
    (point : IncidenceTreeVertex semiGraph root) :
    IncidenceNode (semiGraphCover semiGraph root) :=
  match point with
  | ⟨previous, .vertex (.inl vertexValue), walk⟩ =>
      IncidenceNode.vertex (Sum.inl
        ⟨⟨previous, .vertex (.inl vertexValue), walk⟩,
          vertexValue, rfl⟩)
  | ⟨previous, .vertex (.inr boundary), walk⟩ =>
      let path : IncidenceTreeVertex semiGraph root :=
        ⟨previous, .vertex (.inr boundary), walk⟩
      IncidenceNode.vertex (Sum.inr
        (liftedBoundaryBranch semiGraph root path boundary rfl))
  | ⟨previous, .edge edgeValue, walk⟩ =>
      IncidenceNode.edge
        ⟨⟨previous, .edge edgeValue, walk⟩, edgeValue, rfl⟩
  | ⟨previous, .branch branchValue, walk⟩ =>
      let path : IncidenceTreeVertex semiGraph root :=
        ⟨previous, .branch branchValue, walk⟩
      IncidenceNode.branch
        ⟨liftedEdgeOfBranchPath semiGraph root path branchValue rfl,
          branchValue.2⟩

theorem pathIncidenceNode_of_vertex_original
    (point : IncidenceTreeVertex semiGraph root) (vertex : semiGraph.Vertex)
    (endpoint : point.endpoint = IncidenceNode.vertex (Sum.inl vertex)) :
    pathIncidenceNode semiGraph root point =
      IncidenceNode.vertex (Sum.inl
        (⟨point, vertex, endpoint⟩ : LiftedVertex semiGraph root)) := by
  rcases point with ⟨previous, current, walk⟩
  change current = IncidenceNode.vertex (Sum.inl vertex) at endpoint
  subst current
  rfl

theorem pathIncidenceNode_of_vertex_boundary
    (point : IncidenceTreeVertex semiGraph root)
    (boundary : semiGraph.NonVerticialBranch)
    (endpoint : point.endpoint = IncidenceNode.vertex (Sum.inr boundary)) :
    pathIncidenceNode semiGraph root point =
      IncidenceNode.vertex (Sum.inr
        (liftedBoundaryBranch semiGraph root point boundary endpoint)) := by
  rcases point with ⟨previous, current, walk⟩
  change current = IncidenceNode.vertex (Sum.inr boundary) at endpoint
  subst current
  rfl

theorem pathIncidenceNode_of_edge
    (point : IncidenceTreeVertex semiGraph root) (edge : semiGraph.Edge)
    (endpoint : point.endpoint = IncidenceNode.edge edge) :
    pathIncidenceNode semiGraph root point =
      IncidenceNode.edge
        (⟨point, edge, endpoint⟩ : LiftedEdge semiGraph root) := by
  rcases point with ⟨previous, current, walk⟩
  change current = IncidenceNode.edge edge at endpoint
  subst current
  rfl

theorem pathIncidenceNode_of_branch
    (point : IncidenceTreeVertex semiGraph root)
    (branch : semiGraph.TotalBranch)
    (endpoint : point.endpoint = IncidenceNode.branch branch) :
    pathIncidenceNode semiGraph root point =
      IncidenceNode.branch
        ⟨liftedEdgeOfBranchPath semiGraph root point branch endpoint,
          branch.2⟩ := by
  rcases point with ⟨previous, current, walk⟩
  change current = IncidenceNode.branch branch at endpoint
  subst current
  rfl

/-- Reading the path reconstructed from a universal-tree point returns that
same point. -/
theorem coverIncidencePath_pathIncidenceNode
    (point : IncidenceTreeVertex semiGraph root) :
    coverIncidencePath semiGraph root
        (pathIncidenceNode semiGraph root point) = point := by
  rcases point with ⟨previous, current, walk⟩
  cases current with
  | vertex compactVertex =>
    cases compactVertex with
    | inl vertexValue => rfl
    | inr boundary =>
        simp only [pathIncidenceNode, coverIncidencePath]
        let point : IncidenceTreeVertex semiGraph root :=
          ⟨previous, .vertex (.inr boundary), walk⟩
        rw [liftedBoundaryBranch_val]
        change compactVertexPath semiGraph root
            (liftedEdgeOfBoundaryPath semiGraph root point boundary rfl)
              boundary.1.2 = point
        let branchPoint := branchPathOfBoundaryPath
          semiGraph root point boundary rfl
        have edgeBacktracks :
            branchPath semiGraph root
                (liftedEdgeOfBoundaryPath
                  semiGraph root point boundary rfl) boundary.1.2 =
              branchPoint := by
          apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
          · exact (UniversalVertex.adjacent_liftNeighbor _ _ branchPoint
              (IncidenceNode.edge boundary.1.1) _).symm
          · exact UniversalVertex.liftNeighbor_endpoint _ _ _ _ _
        unfold compactVertexPath
        apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
        · rw [edgeBacktracks]
          exact (UniversalVertex.adjacent_liftNeighbor _ _ point
            (IncidenceNode.branch boundary.1) _).symm
        · have compactEquality :
              compactEndpoint semiGraph boundary.1.1 boundary.1.2 =
                Sum.inr boundary := by
            apply Option.some.inj
            rw [← compactEndpoint_spec]
            exact semiGraph.compactification_coincidence_of_none boundary.2
          have compactEquality' :
              compactEndpoint semiGraph
                  (liftedEdgeOfBoundaryPath
                    semiGraph root point boundary rfl).edge boundary.1.2 =
                Sum.inr boundary := by
            exact compactEquality
          exact congrArg IncidenceNode.vertex compactEquality'.symm
  | edge edgeValue =>
    rfl
  | branch branchValue =>
    simp only [pathIncidenceNode, coverIncidencePath]
    let point : IncidenceTreeVertex semiGraph root :=
      ⟨previous, .branch branchValue, walk⟩
    change branchPath semiGraph root
        (liftedEdgeOfBranchPath
          semiGraph root point branchValue rfl) branchValue.2 = point
    apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
    · exact (UniversalVertex.adjacent_liftNeighbor _ _ point
        (IncidenceNode.edge branchValue.1) _).symm
    · rfl

/-- Reconstructing an incidence node from the path stored by that node
returns the original node. -/
theorem pathIncidenceNode_coverIncidencePath
    (node : IncidenceNode (semiGraphCover semiGraph root)) :
    pathIncidenceNode semiGraph root
        (coverIncidencePath semiGraph root node) = node := by
  cases node with
  | vertex compactVertex =>
      cases compactVertex with
      | inl liftedVertex =>
          rcases liftedVertex with ⟨⟨previous, current, walk⟩,
            vertexValue, endpoint⟩
          change current = IncidenceNode.vertex (Sum.inl vertexValue) at endpoint
          subst current
          rfl
      | inr boundary =>
          rcases boundary with ⟨⟨liftedEdge, branch⟩, nonVerticial⟩
          change pathIncidenceNode semiGraph root
              (compactVertexPath semiGraph root liftedEdge branch) =
            IncidenceNode.vertex (Sum.inr
              (⟨⟨liftedEdge, branch⟩, nonVerticial⟩ :
                (semiGraphCover semiGraph root).NonVerticialBranch))
          let boundary : semiGraph.NonVerticialBranch :=
            ⟨⟨liftedEdge.edge, branch⟩, by
              change semiGraph.coincidence liftedEdge.edge branch = none
              change coincidence semiGraph root liftedEdge branch = none
                at nonVerticial
              unfold coincidence at nonVerticial
              split at nonVerticial
              next sourceNone => exact sourceNone
              next _ _ => cases nonVerticial⟩
          have compactEndpointEquality :
              compactEndpoint semiGraph liftedEdge.edge branch =
                Sum.inr boundary := by
            apply Option.some.inj
            rw [← compactEndpoint_spec]
            exact semiGraph.compactification_coincidence_of_none boundary.2
          have endpointEquality :
              (compactVertexPath semiGraph root liftedEdge branch).endpoint =
                IncidenceNode.vertex (Sum.inr boundary) := by
            rw [compactVertexPath_endpoint, compactEndpointEquality]
          have branchBacktracks :
              branchPathOfBoundaryPath semiGraph root
                  (compactVertexPath semiGraph root liftedEdge branch)
                    boundary endpointEquality =
                branchPath semiGraph root liftedEdge branch := by
            apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
            · exact (UniversalVertex.adjacent_liftNeighbor _ _
                (branchPath semiGraph root liftedEdge branch)
                (IncidenceNode.vertex
                  (compactEndpoint semiGraph liftedEdge.edge branch)) _).symm
            · exact UniversalVertex.liftNeighbor_endpoint _ _ _ _ _
          have edgeBacktracks :
              (liftedEdgeOfBoundaryPath semiGraph root
                (compactVertexPath semiGraph root liftedEdge branch)
                  boundary endpointEquality).path = liftedEdge.path := by
            change UniversalVertex.liftNeighbor _ _
                (branchPathOfBoundaryPath semiGraph root
                  (compactVertexPath semiGraph root liftedEdge branch)
                    boundary endpointEquality)
                (IncidenceNode.edge boundary.1.1) _ = liftedEdge.path
            apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
            · rw [branchBacktracks]
              exact (UniversalVertex.adjacent_liftNeighbor _ _ liftedEdge.path
                (IncidenceNode.branch
                  (⟨liftedEdge.edge, branch⟩ : semiGraph.TotalBranch)) _).symm
            · exact liftedEdge.endpoint_eq
          have liftedEdgeEquality :
              liftedEdgeOfBoundaryPath semiGraph root
                  (compactVertexPath semiGraph root liftedEdge branch)
                    boundary endpointEquality = liftedEdge :=
            LiftedEdge.path_injective semiGraph root edgeBacktracks
          have boundaryEquality :
              liftedBoundaryBranch semiGraph root
                  (compactVertexPath semiGraph root liftedEdge branch)
                    boundary endpointEquality =
                (⟨⟨liftedEdge, branch⟩, nonVerticial⟩ :
                  (semiGraphCover semiGraph root).NonVerticialBranch) := by
            apply Subtype.ext
            apply Sigma.ext liftedEdgeEquality
            exact HEq.rfl
          have nodeFormula :
              pathIncidenceNode semiGraph root
                  (compactVertexPath semiGraph root liftedEdge branch) =
                IncidenceNode.vertex (Sum.inr
                  (liftedBoundaryBranch semiGraph root
                    (compactVertexPath semiGraph root liftedEdge branch)
                      boundary endpointEquality)) := by
            exact pathIncidenceNode_of_vertex_boundary semiGraph root _
              boundary endpointEquality
          rw [nodeFormula, boundaryEquality]
  | edge liftedEdge =>
      rcases liftedEdge with ⟨⟨previous, current, walk⟩,
        edgeValue, endpoint⟩
      change current = IncidenceNode.edge edgeValue at endpoint
      subst current
      rfl
  | branch liftedBranch =>
      rcases liftedBranch with ⟨liftedEdge, branch⟩
      have endpointEquality :
          (branchPath semiGraph root liftedEdge branch).endpoint =
            IncidenceNode.branch
              (⟨liftedEdge.edge, branch⟩ : semiGraph.TotalBranch) :=
        UniversalVertex.liftNeighbor_endpoint _ _ _ _ _
      have edgeBacktracks :
          (liftedEdgeOfBranchPath semiGraph root
            (branchPath semiGraph root liftedEdge branch)
              ⟨liftedEdge.edge, branch⟩ endpointEquality).path =
            liftedEdge.path := by
        apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
        · exact (UniversalVertex.adjacent_liftNeighbor _ _ liftedEdge.path
            (IncidenceNode.branch
              (⟨liftedEdge.edge, branch⟩ : semiGraph.TotalBranch)) _).symm
        · exact liftedEdge.endpoint_eq
      have liftedEdgeEquality :
          liftedEdgeOfBranchPath semiGraph root
              (branchPath semiGraph root liftedEdge branch)
                ⟨liftedEdge.edge, branch⟩ endpointEquality = liftedEdge :=
        LiftedEdge.path_injective semiGraph root edgeBacktracks
      have nodeFormula :
          pathIncidenceNode semiGraph root
              (branchPath semiGraph root liftedEdge branch) =
            IncidenceNode.branch
              ⟨liftedEdgeOfBranchPath semiGraph root
                (branchPath semiGraph root liftedEdge branch)
                  ⟨liftedEdge.edge, branch⟩ endpointEquality, branch⟩ := by
        exact pathIncidenceNode_of_branch semiGraph root _
          ⟨liftedEdge.edge, branch⟩ endpointEquality
      change pathIncidenceNode semiGraph root
          (branchPath semiGraph root liftedEdge branch) =
        IncidenceNode.branch ⟨liftedEdge, branch⟩
      rw [nodeFormula]
      apply congrArg IncidenceNode.branch
      apply Sigma.ext liftedEdgeEquality
      exact HEq.rfl

/-- An edge-path adjacent to a displayed branch-path is the supporting
lifted edge of that branch as soon as their base edges agree. -/
theorem liftedEdge_eq_of_adj_branchPath
    (first second : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch second.edge)
    (adjacent : (UniversalVertex.tree
      (IncidenceNode.incidenceGraph semiGraph)
        (incidenceRoot semiGraph root)).Adj first.path
          (branchPath semiGraph root second branch))
    (edgeEquality : second.edge = first.edge) :
    first = second := by
  apply LiftedEdge.path_injective semiGraph root
  apply UniversalVertex.neighbor_eq_of_endpoint_eq _ _
    (point := branchPath semiGraph root second branch)
  · exact adjacent.symm
  · exact (UniversalVertex.adjacent_liftNeighbor _ _ second.path
      (IncidenceNode.branch
        (⟨second.edge, branch⟩ : semiGraph.TotalBranch)) _).symm
  · rw [first.endpoint_eq, second.endpoint_eq, edgeEquality]

/-- A lifted original-vertex path adjacent to a branch-path is the compact
endpoint lift constructed from that branch. -/
theorem liftedVertex_eq_of_adj_branchPath
    (vertex : LiftedVertex semiGraph root) (edge : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch edge.edge) (baseVertex : semiGraph.Vertex)
    (sourceCoincidence :
      semiGraph.coincidence edge.edge branch = some baseVertex)
    (vertexEquality : vertex.vertex = baseVertex)
    (adjacent : (UniversalVertex.tree
      (IncidenceNode.incidenceGraph semiGraph)
        (incidenceRoot semiGraph root)).Adj vertex.path
          (branchPath semiGraph root edge branch)) :
    vertex =
      ⟨compactVertexPath semiGraph root edge branch, baseVertex, by
        rw [compactVertexPath_endpoint,
          compactEndpoint_of_some semiGraph sourceCoincidence]⟩ := by
  apply LiftedVertex.path_injective semiGraph root
  apply UniversalVertex.neighbor_eq_of_endpoint_eq _ _
    (point := branchPath semiGraph root edge branch)
  · exact adjacent.symm
  · exact UniversalVertex.adjacent_liftNeighbor _ _
      (branchPath semiGraph root edge branch)
      (IncidenceNode.vertex
        (compactEndpoint semiGraph edge.edge branch)) _
  · rw [vertex.endpoint_eq, compactVertexPath_endpoint, vertexEquality,
      compactEndpoint_of_some semiGraph sourceCoincidence]

/-- A displayed branch adjacent to a compactification-boundary path is the
same lifted total branch that defines that boundary node. -/
theorem liftedTotalBranch_eq_of_adj_boundaryPath
    (boundaryEdge : LiftedEdge semiGraph root)
    (boundaryBranch : semiGraph.Branch boundaryEdge.edge)
    (edge : LiftedEdge semiGraph root)
    (branch : semiGraph.Branch edge.edge)
    (adjacent : (UniversalVertex.tree
      (IncidenceNode.incidenceGraph semiGraph)
        (incidenceRoot semiGraph root)).Adj
          (compactVertexPath semiGraph root boundaryEdge boundaryBranch)
          (branchPath semiGraph root edge branch))
    (baseBranchEquality :
      (⟨edge.edge, branch⟩ : semiGraph.TotalBranch) =
        ⟨boundaryEdge.edge, boundaryBranch⟩) :
    (⟨edge, branch⟩ : (semiGraphCover semiGraph root).TotalBranch) =
      ⟨boundaryEdge, boundaryBranch⟩ := by
  have edgeEquality : edge.edge = boundaryEdge.edge :=
    congrArg Sigma.fst baseBranchEquality
  have branchPathEquality :
      branchPath semiGraph root edge branch =
        branchPath semiGraph root boundaryEdge boundaryBranch := by
    apply UniversalVertex.neighbor_eq_of_endpoint_eq _ _
      (point := compactVertexPath semiGraph root boundaryEdge boundaryBranch)
    · exact adjacent
    · exact (UniversalVertex.adjacent_liftNeighbor _ _
        (branchPath semiGraph root boundaryEdge boundaryBranch)
        (IncidenceNode.vertex
          (compactEndpoint semiGraph boundaryEdge.edge boundaryBranch)) _).symm
    · rw [branchPath, branchPath,
        UniversalVertex.liftNeighbor_endpoint,
        UniversalVertex.liftNeighbor_endpoint]
      exact congrArg IncidenceNode.branch baseBranchEquality
  have liftedEdgeEquality : edge = boundaryEdge := by
    apply LiftedEdge.path_injective semiGraph root
    apply UniversalVertex.neighbor_eq_of_endpoint_eq _ _
      (point := branchPath semiGraph root boundaryEdge boundaryBranch)
    · rw [← branchPathEquality]
      exact (UniversalVertex.adjacent_liftNeighbor _ _ edge.path
        (IncidenceNode.branch
          (⟨edge.edge, branch⟩ : semiGraph.TotalBranch)) _).symm
    · exact (UniversalVertex.adjacent_liftNeighbor _ _ boundaryEdge.path
        (IncidenceNode.branch
          (⟨boundaryEdge.edge, boundaryBranch⟩ : semiGraph.TotalBranch)) _).symm
    · rw [edge.endpoint_eq, boundaryEdge.endpoint_eq, edgeEquality]
  cases liftedEdgeEquality
  cases baseBranchEquality
  rfl

/-- Reverse incidence preservation for an edge node followed by a branch
node. -/
theorem coverIncidencePath_edge_branch_adj
    (edge : LiftedEdge semiGraph root)
    (branch : (semiGraphCover semiGraph root).TotalBranch)
    (adjacent : (UniversalVertex.tree
      (IncidenceNode.incidenceGraph semiGraph)
        (incidenceRoot semiGraph root)).Adj
          (coverIncidencePath semiGraph root (IncidenceNode.edge edge))
          (coverIncidencePath semiGraph root (IncidenceNode.branch branch))) :
    (IncidenceNode.incidenceGraph (semiGraphCover semiGraph root)).Adj
      (IncidenceNode.edge edge) (IncidenceNode.branch branch) := by
  rcases branch with ⟨branchEdge, branchValue⟩
  have baseAdjacent := UniversalVertex.endpoint_adj _ _ adjacent
  rw [coverIncidencePath, edge.endpoint_eq, coverIncidencePath,
    branchPath, UniversalVertex.liftNeighbor_endpoint] at baseAdjacent
  have baseEdgeEquality : branchEdge.edge = edge.edge :=
    (IncidenceNode.edge_branch_adj semiGraph edge.edge
      ⟨branchEdge.edge, branchValue⟩).mp baseAdjacent
  have liftedEdgeEquality : edge = branchEdge :=
    liftedEdge_eq_of_adj_branchPath semiGraph root edge branchEdge branchValue
      adjacent baseEdgeEquality
  rw [IncidenceNode.edge_branch_adj]
  exact liftedEdgeEquality.symm

/-- Reverse incidence preservation for a compactified vertex node followed
by a branch node. -/
theorem coverIncidencePath_vertex_branch_adj
    (vertex : (semiGraphCover semiGraph root).CompactVertex)
    (branch : (semiGraphCover semiGraph root).TotalBranch)
    (adjacent : (UniversalVertex.tree
      (IncidenceNode.incidenceGraph semiGraph)
        (incidenceRoot semiGraph root)).Adj
          (coverIncidencePath semiGraph root (IncidenceNode.vertex vertex))
          (coverIncidencePath semiGraph root (IncidenceNode.branch branch))) :
    (IncidenceNode.incidenceGraph (semiGraphCover semiGraph root)).Adj
      (IncidenceNode.vertex vertex) (IncidenceNode.branch branch) := by
  rcases branch with ⟨branchEdge, branchValue⟩
  cases vertex with
  | inl liftedVertex =>
      have baseAdjacent := UniversalVertex.endpoint_adj _ _ adjacent
      rw [coverIncidencePath, liftedVertex.endpoint_eq, coverIncidencePath,
        branchPath, UniversalVertex.liftNeighbor_endpoint] at baseAdjacent
      have baseCoincidence :
          semiGraph.compactification.coincidence branchEdge.edge branchValue =
            some (Sum.inl liftedVertex.vertex) :=
        (IncidenceNode.vertex_branch_adj semiGraph (Sum.inl liftedVertex.vertex)
          ⟨branchEdge.edge, branchValue⟩).mp baseAdjacent
      have sourceCoincidence :
          semiGraph.coincidence branchEdge.edge branchValue =
            some liftedVertex.vertex :=
        IncidenceNode.coincidence_eq_of_compactification_original semiGraph
          ⟨branchEdge.edge, branchValue⟩ liftedVertex.vertex baseCoincidence
      have liftedVertexEquality := liftedVertex_eq_of_adj_branchPath
        semiGraph root liftedVertex branchEdge branchValue liftedVertex.vertex
          sourceCoincidence rfl adjacent
      have liftedCoincidence := coincidence_eq_some_of_eq_some semiGraph root
        branchEdge branchValue liftedVertex.vertex sourceCoincidence
      rw [← liftedVertexEquality] at liftedCoincidence
      rw [IncidenceNode.vertex_branch_adj]
      exact (semiGraphCover semiGraph root).compactification_coincidence_of_some
        liftedCoincidence
  | inr boundary =>
      rcases boundary with ⟨⟨boundaryEdge, boundaryBranch⟩, nonVerticial⟩
      let baseBoundary : semiGraph.NonVerticialBranch :=
        ⟨⟨boundaryEdge.edge, boundaryBranch⟩, by
          change semiGraph.coincidence boundaryEdge.edge boundaryBranch = none
          change coincidence semiGraph root boundaryEdge boundaryBranch = none
            at nonVerticial
          unfold coincidence at nonVerticial
          split at nonVerticial
          next sourceNone => exact sourceNone
          next _ _ => cases nonVerticial⟩
      have compactEndpointEquality :
          compactEndpoint semiGraph boundaryEdge.edge boundaryBranch =
            Sum.inr baseBoundary := by
        apply Option.some.inj
        rw [← compactEndpoint_spec]
        exact semiGraph.compactification_coincidence_of_none baseBoundary.2
      have baseAdjacent := UniversalVertex.endpoint_adj _ _ adjacent
      rw [coverIncidencePath, compactVertexPath_endpoint,
        compactEndpointEquality, coverIncidencePath, branchPath,
        UniversalVertex.liftNeighbor_endpoint] at baseAdjacent
      have baseBranchEquality :
          (⟨branchEdge.edge, branchValue⟩ : semiGraph.TotalBranch) =
            baseBoundary.1 :=
        IncidenceNode.totalBranch_eq_of_compactification_boundary semiGraph
          ⟨branchEdge.edge, branchValue⟩ baseBoundary
            ((IncidenceNode.vertex_branch_adj semiGraph (Sum.inr baseBoundary)
              ⟨branchEdge.edge, branchValue⟩).mp baseAdjacent)
      have liftedBranchEquality :=
        liftedTotalBranch_eq_of_adj_boundaryPath semiGraph root
          boundaryEdge boundaryBranch branchEdge branchValue adjacent
            baseBranchEquality
      rw [IncidenceNode.vertex_branch_adj]
      cases liftedBranchEquality
      exact (semiGraphCover semiGraph root).compactification_coincidence_of_none
        nonVerticial

/-- Faithful incidence in the lifted semi-graph is exactly adjacency in the
universal reduced-walk tree. -/
theorem coverIncidencePath_adj_iff
    (first second : IncidenceNode (semiGraphCover semiGraph root)) :
    (IncidenceNode.incidenceGraph (semiGraphCover semiGraph root)).Adj
        first second ↔
      (UniversalVertex.tree (IncidenceNode.incidenceGraph semiGraph)
        (incidenceRoot semiGraph root)).Adj
          (coverIncidencePath semiGraph root first)
          (coverIncidencePath semiGraph root second) := by
  constructor
  · exact fun adjacent =>
      (coverIncidenceGraphHom semiGraph root).map_rel adjacent
  · intro adjacent
    cases first with
    | vertex firstVertex =>
        cases second with
        | vertex secondVertex =>
            have baseAdjacent := UniversalVertex.endpoint_adj _ _ adjacent
            rw [coverIncidencePath_vertex_endpoint,
              coverIncidencePath_vertex_endpoint] at baseAdjacent
            simp [IncidenceNode.incidenceGraph,
              IncidenceNode.incidenceRel, SimpleGraph.fromRel_adj]
              at baseAdjacent
        | edge secondEdge =>
            have baseAdjacent := UniversalVertex.endpoint_adj _ _ adjacent
            rw [coverIncidencePath_vertex_endpoint,
              coverIncidencePath_edge_endpoint] at baseAdjacent
            simp [IncidenceNode.incidenceGraph,
              IncidenceNode.incidenceRel, SimpleGraph.fromRel_adj]
              at baseAdjacent
        | branch secondBranch =>
            exact coverIncidencePath_vertex_branch_adj semiGraph root
              firstVertex secondBranch adjacent
    | edge firstEdge =>
        cases second with
        | vertex secondVertex =>
            have baseAdjacent := UniversalVertex.endpoint_adj _ _ adjacent
            rw [coverIncidencePath_edge_endpoint,
              coverIncidencePath_vertex_endpoint] at baseAdjacent
            simp [IncidenceNode.incidenceGraph,
              IncidenceNode.incidenceRel, SimpleGraph.fromRel_adj]
              at baseAdjacent
        | edge secondEdge =>
            have baseAdjacent := UniversalVertex.endpoint_adj _ _ adjacent
            rw [coverIncidencePath_edge_endpoint,
              coverIncidencePath_edge_endpoint] at baseAdjacent
            simp [IncidenceNode.incidenceGraph,
              IncidenceNode.incidenceRel, SimpleGraph.fromRel_adj]
              at baseAdjacent
        | branch secondBranch =>
            exact coverIncidencePath_edge_branch_adj semiGraph root
              firstEdge secondBranch adjacent
    | branch firstBranch =>
        cases second with
        | vertex secondVertex =>
            rw [SimpleGraph.adj_comm]
            exact coverIncidencePath_vertex_branch_adj semiGraph root
              secondVertex firstBranch adjacent.symm
        | edge secondEdge =>
            rw [SimpleGraph.adj_comm]
            exact coverIncidencePath_edge_branch_adj semiGraph root
              secondEdge firstBranch adjacent.symm
        | branch secondBranch =>
            have baseAdjacent := UniversalVertex.endpoint_adj _ _ adjacent
            rw [coverIncidencePath_branch_endpoint,
              coverIncidencePath_branch_endpoint] at baseAdjacent
            simp [IncidenceNode.incidenceGraph,
              IncidenceNode.incidenceRel, SimpleGraph.fromRel_adj]
              at baseAdjacent

/-- The faithful incidence graph of the lifted semi-graph is the universal
reduced-walk tree itself. -/
noncomputable def coverIncidenceGraphIso :
    IncidenceNode.incidenceGraph (semiGraphCover semiGraph root) ≃g
      UniversalVertex.tree (IncidenceNode.incidenceGraph semiGraph)
        (incidenceRoot semiGraph root) where
  toFun := coverIncidencePath semiGraph root
  invFun := pathIncidenceNode semiGraph root
  left_inv := pathIncidenceNode_coverIncidencePath semiGraph root
  right_inv := coverIncidencePath_pathIncidenceNode semiGraph root
  map_rel_iff' := fun {first second} =>
    (coverIncidencePath_adj_iff semiGraph root first second).symm

/-- The faithful incidence graph of the combinatorial universal cover is
connected because it is the universal reduced-walk tree. -/
theorem coverIncidenceGraph_connected :
    (IncidenceNode.incidenceGraph
      (semiGraphCover semiGraph root)).Connected :=
  (SimpleGraph.Iso.connected_iff
    (coverIncidenceGraphIso semiGraph root)).mpr
      (UniversalVertex.tree_connected
        (IncidenceNode.incidenceGraph semiGraph)
          (incidenceRoot semiGraph root))

/-- The combinatorial universal covering semi-graph is connected. -/
theorem semiGraphCover_isConnected :
    (semiGraphCover semiGraph root).IsConnected := by
  let rootLift : LiftedVertex semiGraph root :=
    ⟨UniversalVertex.base (IncidenceNode.incidenceGraph semiGraph)
      (incidenceRoot semiGraph root), root, rfl⟩
  letI : Nonempty (semiGraphCover semiGraph root).Vertex := ⟨rootLift⟩
  exact IncidenceNode.isConnected_of_incidenceGraph_connected
    (semiGraphCover semiGraph root) (coverIncidenceGraph_connected semiGraph root)

/-- Projection of the combinatorial universal cover to the source
semi-graph. -/
noncomputable def projection :
    (semiGraphCover semiGraph root).Hom semiGraph where
  vertexMap := LiftedVertex.vertex
  edgeMap := LiftedEdge.edge
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro edge branch vertex sourceCoincidence
    unfold semiGraphCover at sourceCoincidence
    simp only at sourceCoincidence
    unfold coincidence at sourceCoincidence
    split at sourceCoincidence
    next noCoincidence => cases sourceCoincidence
    next targetVertex targetCoincidence =>
      have vertexEquality := Option.some.inj sourceCoincidence
      cases vertexEquality
      exact targetCoincidence

/-- The universal-cover projection preserves and reflects nonverticial
branches. -/
theorem projection_isProper :
    (projection semiGraph root).IsProper := by
  intro edge branch
  constructor
  · rintro ⟨vertex, coincidence⟩
    exact ⟨vertex.vertex,
      (projection semiGraph root).map_coincidence
        edge branch vertex coincidence⟩
  · rintro ⟨vertex, coincidence⟩
    change semiGraph.coincidence edge.edge branch = some vertex at coincidence
    let liftedVertex : LiftedVertex semiGraph root :=
      ⟨compactVertexPath semiGraph root edge branch, vertex, by
        rw [compactVertexPath_endpoint,
          compactEndpoint_of_some semiGraph coincidence]⟩
    refine ⟨liftedVertex, ?_⟩
    change SourceSemiGraphUniversalCover.coincidence semiGraph root edge branch =
      some liftedVertex
    simpa only [liftedVertex] using
      coincidence_eq_some_of_eq_some semiGraph root edge branch vertex coincidence

/-- Lift the first half of an incident branch, from an original lifted
vertex to the branch node. -/
noncomputable def incidentBranchPath
    (vertex : LiftedVertex semiGraph root)
    (branch : semiGraph.IncidentBranch vertex.vertex) :
    IncidenceTreeVertex semiGraph root :=
  UniversalVertex.liftNeighbor _ _ vertex.path
    (IncidenceNode.branch branch.1)
    (by
      rw [vertex.endpoint_eq, IncidenceNode.vertex_branch_adj]
      exact semiGraph.compactification_coincidence_of_some branch.2)

/-- Continue a lifted incident branch to its unique lifted edge. -/
noncomputable def incidentEdge
    (vertex : LiftedVertex semiGraph root)
    (branch : semiGraph.IncidentBranch vertex.vertex) :
    LiftedEdge semiGraph root where
  path := UniversalVertex.liftNeighbor _ _
    (incidentBranchPath semiGraph root vertex branch)
    (IncidenceNode.edge branch.1.edge)
    (by
      rw [incidentBranchPath, UniversalVertex.liftNeighbor_endpoint,
        IncidenceNode.branch_edge_adj])
  edge := branch.1.edge
  endpoint_eq := UniversalVertex.liftNeighbor_endpoint _ _ _ _ _

/-- The edge-to-branch lift returns to the intermediate branch path. -/
theorem branchPath_incidentEdge
    (vertex : LiftedVertex semiGraph root)
    (branch : semiGraph.IncidentBranch vertex.vertex) :
    branchPath semiGraph root (incidentEdge semiGraph root vertex branch)
        branch.1.2 =
      incidentBranchPath semiGraph root vertex branch := by
  change UniversalVertex.liftNeighbor _ _
      (UniversalVertex.liftNeighbor _ _
        (incidentBranchPath semiGraph root vertex branch)
        (IncidenceNode.edge branch.1.edge) _)
      (IncidenceNode.branch branch.1) _ =
    incidentBranchPath semiGraph root vertex branch
  apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
  · exact (UniversalVertex.adjacent_liftNeighbor _ _
      (incidentBranchPath semiGraph root vertex branch)
      (IncidenceNode.edge branch.1.edge) _).symm
  · exact UniversalVertex.liftNeighbor_endpoint _ _ _ _ _

/-- Traversing the lifted edge back along the selected branch returns to the
original lifted vertex. -/
theorem compactVertexPath_incidentEdge
    (vertex : LiftedVertex semiGraph root)
    (branch : semiGraph.IncidentBranch vertex.vertex) :
    compactVertexPath semiGraph root
        (incidentEdge semiGraph root vertex branch) branch.1.2 =
      vertex.path := by
  unfold compactVertexPath
  apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
  · rw [branchPath_incidentEdge semiGraph root vertex branch]
    exact (UniversalVertex.adjacent_liftNeighbor _ _ vertex.path
      (IncidenceNode.branch branch.1) _).symm
  · rw [vertex.endpoint_eq]
    change IncidenceNode.vertex (Sum.inl vertex.vertex) =
      IncidenceNode.vertex
        (compactEndpoint semiGraph branch.1.1 branch.1.2)
    rw [compactEndpoint_of_some semiGraph branch.2]

/-- Reversing the lifted incidence of an existing cover branch recovers its
intermediate branch path. -/
theorem incidentBranchPath_projection
    (vertex : LiftedVertex semiGraph root)
    (branch : (semiGraphCover semiGraph root).IncidentBranch vertex) :
    incidentBranchPath semiGraph root vertex
        ((projection semiGraph root).incidentBranchMap vertex branch) =
      branchPath semiGraph root branch.1.1 branch.1.2 := by
  rcases branch with ⟨⟨edge, branch⟩, coincidence⟩
  have endpointEquality := compactVertexPath_eq_of_coincidence
    semiGraph root edge branch vertex coincidence
  apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
  · rw [← endpointEquality]
    exact (UniversalVertex.adjacent_liftNeighbor _ _
      (branchPath semiGraph root edge branch)
      (IncidenceNode.vertex (compactEndpoint semiGraph edge.edge branch)) _).symm
  · exact UniversalVertex.liftNeighbor_endpoint _ _ _ _ _

/-- Reversing both halves of an existing lifted incidence recovers its
lifted edge. -/
theorem incidentEdge_projection
    (vertex : LiftedVertex semiGraph root)
    (branch : (semiGraphCover semiGraph root).IncidentBranch vertex) :
    incidentEdge semiGraph root vertex
        ((projection semiGraph root).incidentBranchMap vertex branch) =
      branch.1.1 := by
  apply LiftedEdge.path_injective semiGraph root
  rcases branch with ⟨⟨edge, branch⟩, coincidence⟩
  change UniversalVertex.liftNeighbor _ _
      (incidentBranchPath semiGraph root vertex
        ((projection semiGraph root).incidentBranchMap vertex
          ⟨⟨edge, branch⟩, coincidence⟩))
      (IncidenceNode.edge edge.edge) _ = edge.path
  have branchPathEquality := incidentBranchPath_projection semiGraph root
    vertex ⟨⟨edge, branch⟩, coincidence⟩
  apply UniversalVertex.liftNeighbor_eq_of_adj_of_endpoint_eq
  · rw [branchPathEquality]
    exact (UniversalVertex.adjacent_liftNeighbor _ _ edge.path
      (IncidenceNode.branch (⟨edge.edge, branch⟩ : semiGraph.TotalBranch)) _).symm
  · exact edge.endpoint_eq

/-- Inverse to the incident-branch map of the universal-cover projection. -/
noncomputable def liftIncidentBranch
    (vertex : LiftedVertex semiGraph root) :
    semiGraph.IncidentBranch vertex.vertex →
      (semiGraphCover semiGraph root).IncidentBranch vertex
  | branch =>
      ⟨⟨incidentEdge semiGraph root vertex branch, branch.1.2⟩, by
        have targetCoincidence :
            semiGraph.coincidence
                (incidentEdge semiGraph root vertex branch).edge branch.1.2 =
              some vertex.vertex := by
          simpa only [incidentEdge, SourceSemiGraph.coincidenceTotal,
            SourceSemiGraph.TotalBranch.edge] using
            branch.2
        change SourceSemiGraphUniversalCover.coincidence semiGraph root
          (incidentEdge semiGraph root vertex branch) branch.1.2 = some vertex
        rw [coincidence_eq_some_of_eq_some semiGraph root _ _ _
          targetCoincidence]
        apply congrArg some
        apply LiftedVertex.path_injective semiGraph root
        exact compactVertexPath_incidentEdge semiGraph root vertex branch⟩

/-- The incident-branch projection is bijective at every lifted vertex. -/
theorem projection_incidentBranch_bijective
    (vertex : LiftedVertex semiGraph root) :
    Function.Bijective
      ((projection semiGraph root).incidentBranchMap vertex) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨liftIncidentBranch semiGraph root vertex, ?_, ?_⟩
  · intro branch
    apply Subtype.ext
    apply Sigma.ext
    · exact incidentEdge_projection semiGraph root vertex branch
    · rfl
  · intro branch
    apply Subtype.ext
    rcases branch with ⟨⟨edge, branch⟩, coincidence⟩
    rfl

/-- The reduced-walk construction is a graph-covering in the literal source
semi-graph sense: a proper excision. -/
theorem projection_isGraphCovering :
    (projection semiGraph root).IsGraphCovering :=
  ⟨projection_isProper semiGraph root,
    projection_incidentBranch_bijective semiGraph root⟩

end SourceSemiGraphUniversalCover

/-! ## Universal covers of the constructed connected Galois levels -/

namespace SourceGaloisCombinatorialUniversalCover

open SourceCombinatorialUniversalCover
open SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel

noncomputable section

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)

/-- The finite semigraph is taken directly from the connected Galois object
constructed in `B(G)`. -/
abbrev LevelSemiGraph : SourceSemiGraph.{u} :=
  level.semiGraph

/-- The selected point of the Galois object supplies the universal-cover
root; it is not an additional output field. -/
abbrev LevelRoot : (LevelSemiGraph diagram root level).Vertex :=
  level.rootVertex

/-- The combinatorial universal semigraph cover of the constructed level. -/
noncomputable abbrev Cover : SourceSemiGraph.{u} :=
  SourceSemiGraphUniversalCover.semiGraphCover
    (LevelSemiGraph diagram root level) (LevelRoot diagram root level)

/-- Projection to the constructed finite Galois level. -/
noncomputable abbrev projection :
    (Cover diagram root level).Hom (LevelSemiGraph diagram root level) :=
  SourceSemiGraphUniversalCover.projection
    (LevelSemiGraph diagram root level) (LevelRoot diagram root level)

/-- The universal-cover projection is a proper excision. -/
theorem projection_isGraphCovering :
    (projection diagram root level).IsGraphCovering :=
  SourceSemiGraphUniversalCover.projection_isGraphCovering
    (LevelSemiGraph diagram root level) (LevelRoot diagram root level)

/-- Faithful incidence graph of the constructed finite Galois level. -/
abbrev IncidenceGraph :=
  IncidenceNode.incidenceGraph (LevelSemiGraph diagram root level)

/-- Root selected by the pointed Galois object. -/
abbrev IncidenceRoot :
    IncidenceNode (LevelSemiGraph diagram root level) :=
  IncidenceNode.vertex (Sum.inl (LevelRoot diagram root level))

/-- Vertices of the universal incidence tree. -/
abbrev IncidenceTreeVertex :=
  UniversalVertex (IncidenceGraph diagram root level)
    (IncidenceRoot diagram root level)

/-- Faithful incidence graph of the source semigraph. -/
abbrev BaseIncidenceGraph :=
  IncidenceNode.incidenceGraph diagram.base

/-- Incidence projection induced by the finite-etale Galois level. -/
noncomputable abbrev BaseIncidenceProjection :
    IncidenceGraph diagram root level →g BaseIncidenceGraph diagram :=
  IncidenceNode.properIncidenceGraphHom (LevelSemiGraph diagram root level)
    level.projection level.projection_isProper

/-- Every base vertex has a lift to a connected Galois level.  The lift is
obtained from the selected root point and path lifting in the finite-etale
semigraph, rather than supplied as level data. -/
theorem levelProjection_vertex_surjective :
    Function.Surjective
      (level.projection.vertexMap :
        (LevelSemiGraph diagram root level).Vertex → diagram.base.Vertex) := by
  intro target
  rcases diagram.connected with connected | isolated
  · let rootComponent :
        SourceSemiGraphOfAnabelioids.GluedObject.CoverVertexComponent
          diagram level.object root :=
      Quotient.mk'' level.point
    obtain ⟨targetComponent, _path⟩ :=
      SourceSemiGraphOfAnabelioids.GluedObject.exists_path_lift
        diagram root level.object rootComponent (connected.2.2 root target)
    exact ⟨⟨target, targetComponent⟩, rfl⟩
  · letI : IsEmpty diagram.base.Vertex := isolated.1
    have contradiction : False := isEmptyElim root
    exact contradiction.elim

/-- Every base edge has a lift to a connected Galois level. -/
theorem levelProjection_edge_surjective :
    Function.Surjective
      (level.projection.edgeMap :
        (LevelSemiGraph diagram root level).Edge → diagram.base.Edge) := by
  intro target
  let reference :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
      diagram root target
  obtain ⟨liftedVertex, vertexEquality⟩ :=
    levelProjection_vertex_surjective diagram root level reference.vertex
  rcases liftedVertex with ⟨baseVertex, vertexComponent⟩
  change baseVertex = reference.vertex at vertexEquality
  subst baseVertex
  obtain ⟨edgeComponent, _componentEquality⟩ :=
    SourceSemiGraphOfAnabelioids.GluedObject.coverComponentMap_surjective
      diagram root level.object reference vertexComponent
  exact ⟨⟨target, edgeComponent⟩, rfl⟩

/-- Every total base branch has a lift to a connected Galois level. -/
theorem levelProjection_totalBranch_surjective :
    Function.Surjective
      (level.projection.totalBranchMap :
        (LevelSemiGraph diagram root level).TotalBranch →
          diagram.base.TotalBranch) := by
  rintro ⟨targetEdge, targetBranch⟩
  obtain ⟨liftedEdge, edgeEquality⟩ :=
    levelProjection_edge_surjective diagram root level targetEdge
  rcases liftedEdge with ⟨baseEdge, edgeComponent⟩
  change baseEdge = targetEdge at edgeEquality
  subst baseEdge
  exact ⟨⟨⟨targetEdge, edgeComponent⟩, targetBranch⟩, rfl⟩

/-- The faithful incidence projection of a connected Galois level is
surjective on all node kinds, including open branches. -/
theorem baseIncidenceProjection_surjective :
    Function.Surjective (BaseIncidenceProjection diagram root level) := by
  intro target
  cases target with
  | vertex target =>
      cases target with
      | inl vertex =>
          obtain ⟨source, equality⟩ :=
            levelProjection_vertex_surjective diagram root level vertex
          refine ⟨IncidenceNode.vertex (Sum.inl source), ?_⟩
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_original]
          exact congrArg (fun value ↦ IncidenceNode.vertex (Sum.inl value))
            equality
      | inr branch =>
          obtain ⟨sourceBranch, branchEquality⟩ :=
            levelProjection_totalBranch_surjective diagram root level branch.1
          have sourceNone :
              (LevelSemiGraph diagram root level).coincidenceTotal
                sourceBranch = none := by
            cases sourceCoincidence :
                (LevelSemiGraph diagram root level).coincidenceTotal
                  sourceBranch with
            | none => rfl
            | some vertex =>
                have mapped := level.projection.map_coincidence
                  sourceBranch.1 sourceBranch.2 vertex sourceCoincidence
                change diagram.base.coincidenceTotal
                    (level.projection.totalBranchMap sourceBranch) =
                  some _ at mapped
                rw [branchEquality, branch.2] at mapped
                cases mapped
          let source :
              (LevelSemiGraph diagram root level).NonVerticialBranch :=
            ⟨sourceBranch, sourceNone⟩
          refine ⟨IncidenceNode.vertex (Sum.inr source), ?_⟩
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary]
          apply congrArg (fun value ↦ IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          exact branchEquality
  | edge edge =>
      obtain ⟨source, equality⟩ :=
        levelProjection_edge_surjective diagram root level edge
      refine ⟨IncidenceNode.edge source, ?_⟩
      rw [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge]
      exact congrArg IncidenceNode.edge equality
  | branch branch =>
      obtain ⟨source, equality⟩ :=
        levelProjection_totalBranch_surjective diagram root level branch
      refine ⟨IncidenceNode.branch source, ?_⟩
      rw [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch, equality]

/-- Endpoint of the composite cover over the source incidence graph. -/
noncomputable def compositeEndpoint
    (point : IncidenceTreeVertex diagram root level) :
    IncidenceNode diagram.base :=
  BaseIncidenceProjection diagram root level point.endpoint

/-- A fiber of the composite cover over one source incidence node. -/
abbrev CompositeFiber (basePoint : IncidenceNode diagram.base) :=
  {point : IncidenceTreeVertex diagram root level //
    compositeEndpoint diagram root level point = basePoint}

/-- The universal incidence tree is connected and acyclic. -/
theorem incidenceTree_isTree :
    (UniversalVertex.tree (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level)).IsTree :=
  UniversalVertex.tree_isTree (IncidenceGraph diagram root level)
    (IncidenceRoot diagram root level)

/-- The complete automorphism group acts on the finite-level incidence
graph through the action derived in #55. -/
noncomputable abbrev IncidenceActionHom :
    Aut level.object →*
      UniversalVertex.graphAutomorphismSubgroup
        (IncidenceGraph diagram root level) :=
  UniversalVertex.incidenceAutomorphismHom
    (level.automorphismAction)

/-- The composite deck group retains `Aut(level.object)` itself, not merely
its image in incidence-graph permutations. -/
noncomputable abbrev DeckGroup :=
  UniversalVertex.CompositeDeckTransformation
    (IncidenceGraph diagram root level)
    (IncidenceRoot diagram root level)
    (IncidenceActionHom diagram root level)

/-- The derived finite Galois action is transitive on every fiber of the
faithful incidence projection. -/
theorem incidenceEndpoint_automorphismOrbit
    (first second : IncidenceNode (LevelSemiGraph diagram root level))
    (sameBase : BaseIncidenceProjection diagram root level first =
      BaseIncidenceProjection diagram root level second) :
    ∃ automorphism : Aut level.object,
      IncidenceNode.incidencePerm (LevelSemiGraph diagram root level)
        level.automorphismAction automorphism first = second := by
  cases first with
  | vertex first =>
      cases second with
      | vertex second =>
          cases first with
          | inl first =>
              cases second with
              | inl second =>
                  have sameVertex : level.projection.vertexMap first =
                      level.projection.vertexMap second := by
                    exact Sum.inl.inj (IncidenceNode.vertex.inj sameBase)
                  obtain ⟨automorphism, equality⟩ :=
                    vertexAction_transitive_on_projection_fiber diagram root
                      level first second sameVertex
                  refine ⟨automorphism, ?_⟩
                  rw [IncidenceNode.incidencePerm_vertex]
                  exact congrArg (fun value ↦
                    IncidenceNode.vertex (Sum.inl value)) equality
              | inr second =>
                  have impossible := IncidenceNode.vertex.inj sameBase
                  cases impossible
          | inr first =>
              cases second with
              | inl second =>
                  have impossible := IncidenceNode.vertex.inj sameBase
                  cases impossible
              | inr second =>
                  have sameBranch :
                      level.projection.totalBranchMap first.1 =
                        level.projection.totalBranchMap second.1 := by
                    exact congrArg Subtype.val <|
                      Sum.inr.inj (IncidenceNode.vertex.inj sameBase)
                  have sameEdge : level.projection.edgeMap first.1.edge =
                      level.projection.edgeMap second.1.edge :=
                    Sigma.mk.inj_iff.mp sameBranch |>.1
                  obtain ⟨automorphism, edgeEquality⟩ :=
                    edgeAction_transitive_on_projection_fiber diagram root
                      level first.1.edge second.1.edge sameEdge
                  refine ⟨automorphism, ?_⟩
                  rw [IncidenceNode.incidencePerm_vertex]
                  apply congrArg (fun value ↦
                    IncidenceNode.vertex (Sum.inr value))
                  apply Subtype.ext
                  apply Sigma.ext edgeEquality
                  exact Sigma.mk.inj_iff.mp sameBranch |>.2
      | edge second =>
          cases sameBase
      | branch second =>
          cases sameBase
  | edge first =>
      cases second with
      | vertex second =>
          cases sameBase
      | edge second =>
          have sameEdge : level.projection.edgeMap first =
              level.projection.edgeMap second :=
            IncidenceNode.edge.inj sameBase
          obtain ⟨automorphism, equality⟩ :=
            edgeAction_transitive_on_projection_fiber diagram root level
              first second sameEdge
          refine ⟨automorphism, ?_⟩
          rw [IncidenceNode.incidencePerm_edge]
          exact congrArg IncidenceNode.edge equality
      | branch second =>
          cases sameBase
  | branch first =>
      cases second with
      | vertex second =>
          cases sameBase
      | edge second =>
          cases sameBase
      | branch second =>
          have sameBranch : level.projection.totalBranchMap first =
              level.projection.totalBranchMap second :=
            IncidenceNode.branch.inj sameBase
          have sameEdge : level.projection.edgeMap first.edge =
              level.projection.edgeMap second.edge :=
            Sigma.mk.inj_iff.mp sameBranch |>.1
          obtain ⟨automorphism, edgeEquality⟩ :=
            edgeAction_transitive_on_projection_fiber diagram root level
              first.edge second.edge sameEdge
          refine ⟨automorphism, ?_⟩
          rw [IncidenceNode.incidencePerm_branch]
          apply congrArg IncidenceNode.branch
          apply Sigma.ext edgeEquality
          exact Sigma.mk.inj_iff.mp sameBranch |>.2

/-- Finite Galois symmetries change only the level coordinate and therefore
lie over the identity of the source incidence graph. -/
theorem baseIncidenceProjection_incidencePerm
    (automorphism : Aut level.object)
    (point : IncidenceNode (LevelSemiGraph diagram root level)) :
    BaseIncidenceProjection diagram root level
        (IncidenceNode.incidencePerm (LevelSemiGraph diagram root level)
          level.automorphismAction automorphism point) =
      BaseIncidenceProjection diagram root level point := by
  cases point with
  | vertex point =>
      cases point with
      | inl vertex => rfl
      | inr branch =>
          rw [IncidenceNode.incidencePerm_vertex]
          change BaseIncidenceProjection diagram root level
              (IncidenceNode.vertex (Sum.inr
                (IncidenceNode.nonVerticialBranchPerm
                  (LevelSemiGraph diagram root level)
                  level.automorphismAction automorphism branch))) = _
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary,
            IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary]
          apply congrArg (fun value ↦ IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          rfl
  | edge edge => rfl
  | branch branch => rfl

/-- Every composite deck transformation preserves the source endpoint. -/
theorem compositeEndpoint_deck_apply
    (transformation : DeckGroup diagram root level)
    (point : IncidenceTreeVertex diagram root level) :
    compositeEndpoint diagram root level
        (UniversalVertex.CompositeDeckTransformation.treePerm
          transformation point) =
      compositeEndpoint diagram root level point := by
  unfold compositeEndpoint
  rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply]
  exact baseIncidenceProjection_incidencePerm diagram root level
    (UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation)
    point.endpoint

/-- The complete composite deck group is transitive on every nonempty fiber
over the source incidence graph. -/
theorem deckAction_transitive_compositeFiber
    (first second : IncidenceTreeVertex diagram root level)
    (sameFiber : compositeEndpoint diagram root level first =
      compositeEndpoint diagram root level second) :
    ∃ transformation : DeckGroup diagram root level,
      UniversalVertex.CompositeDeckTransformation.treePerm
        transformation first = second := by
  apply UniversalVertex.CompositeDeckTransformation.exists_treePerm_eq
  exact incidenceEndpoint_automorphismOrbit diagram root level
    first.endpoint second.endpoint sameFiber

/-- The constituent fiber used to detect finite Galois symmetries that are
invisible on the underlying incidence graph. -/
abbrev ConstituentFiber :=
  (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).obj
    level.object

/-- The faithful realization of the composite cover couples its incidence
tree with the selected constituent fiber. -/
abbrev FaithfulRealization :=
  IncidenceTreeVertex diagram root level ×
    ConstituentFiber diagram root level

/-- The full composite deck group acts faithfully on incidence plus
constituent data. -/
theorem deckAction_faithful :
    FaithfulSMul (DeckGroup diagram root level)
      (FaithfulRealization diagram root level) := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  letI : FaithfulSMul (Aut level.object)
      (ConstituentFiber diagram root level) :=
    { eq_of_smul_eq_smul := by
        intro first second actionEquality
        apply PreGaloisCategory.evaluation_aut_injective_of_isConnected
          (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root)
          level.object level.point
        exact actionEquality level.point }
  letI : Nonempty (IncidenceTreeVertex diagram root level) :=
    ⟨UniversalVertex.base (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level)⟩
  letI : Nonempty (ConstituentFiber diagram root level) :=
    ⟨level.point⟩
  exact UniversalVertex.CompositeDeckTransformation.constituentFiber_faithful
    (ConstituentFiber diagram root level)

/-- Under countable-base hypotheses the constructed composite deck group is
countable and discrete. -/
theorem deckGroup_countable
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    Countable (DeckGroup diagram root level) := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  letI : Countable (LevelSemiGraph diagram root level).Vertex :=
    SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.vertex_countable
      diagram root level
  letI : Countable (LevelSemiGraph diagram root level).Edge :=
    SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.edge_countable
      diagram root level
  letI : Countable (Aut level.object) := Finite.to_countable
  infer_instance

/-- Each finite-level composite deck group carries the discrete topology. -/
theorem deckGroup_discreteTopology :
    DiscreteTopology (DeckGroup diagram root level) :=
  inferInstance

/-! ### Refinement of constructed Galois levels -/

/-- Faithful-incidence map derived from a pointed Galois refinement. -/
noncomputable abbrev RefinementIncidenceMap
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    IncidenceGraph diagram root finer →g
      IncidenceGraph diagram root coarser :=
  IncidenceNode.properIncidenceGraphHom (LevelSemiGraph diagram root finer)
    (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition
      diagram root refinement)
    (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_isProper
      diagram root refinement)

/-- The incidence refinement preserves the point-selected root. -/
@[simp]
theorem refinementIncidenceMap_root
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    RefinementIncidenceMap diagram root refinement
        (IncidenceRoot diagram root finer) =
      IncidenceRoot diagram root coarser := by
  change IncidenceNode.vertex (Sum.inl
      ((SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition
        diagram root refinement).vertexMap finer.rootVertex)) = _
  rw [SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_rootVertex]

/-- Refinement intertwines the Galois incidence actions, with the target
automorphism derived by Galois descent. -/
theorem refinement_incidence_commutes
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (automorphism : Aut finer.object)
    (point : IncidenceNode (LevelSemiGraph diagram root finer)) :
    RefinementIncidenceMap diagram root refinement
        (IncidenceNode.incidencePerm (LevelSemiGraph diagram root finer)
          finer.automorphismAction automorphism point) =
      IncidenceNode.incidencePerm (LevelSemiGraph diagram root coarser)
        coarser.automorphismAction
          (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition
            diagram root refinement automorphism)
          (RefinementIncidenceMap diagram root refinement point) := by
  cases point with
  | vertex point =>
      cases point with
      | inl vertex =>
          rw [IncidenceNode.incidencePerm_vertex]
          change IncidenceNode.vertex (Sum.inl _) = _
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_original,
            IncidenceNode.incidencePerm_vertex]
          apply congrArg (fun value ↦ IncidenceNode.vertex (Sum.inl value))
          exact SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_vertex_automorphism
            diagram root refinement automorphism vertex
      | inr branch =>
          rw [IncidenceNode.incidencePerm_vertex]
          change RefinementIncidenceMap diagram root refinement
              (IncidenceNode.vertex (Sum.inr
                (IncidenceNode.nonVerticialBranchPerm
                  (LevelSemiGraph diagram root finer)
                  finer.automorphismAction automorphism branch))) = _
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary,
            IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary,
            IncidenceNode.incidencePerm_vertex]
          change IncidenceNode.vertex (Sum.inr _) =
            IncidenceNode.vertex (Sum.inr _)
          apply congrArg (fun value ↦ IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          exact SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_branch_automorphism
            diagram root refinement automorphism branch.1
  | edge edge =>
      rw [IncidenceNode.incidencePerm_edge,
        IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge,
        IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge,
        IncidenceNode.incidencePerm_edge]
      apply congrArg IncidenceNode.edge
      exact SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_edge_automorphism
        diagram root refinement automorphism edge
  | branch branch =>
      rw [IncidenceNode.incidencePerm_branch,
        IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch,
        IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch,
        IncidenceNode.incidencePerm_branch]
      apply congrArg IncidenceNode.branch
      exact SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_branch_automorphism
        diagram root refinement automorphism branch

/-- Galois refinement lies over the identity of the source faithful
incidence graph. -/
theorem baseIncidenceProjection_refinement
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (point : IncidenceNode (LevelSemiGraph diagram root finer)) :
    BaseIncidenceProjection diagram root coarser
        (RefinementIncidenceMap diagram root refinement point) =
      BaseIncidenceProjection diagram root finer point := by
  cases point with
  | vertex point =>
      cases point with
      | inl vertex => rfl
      | inr branch =>
          change BaseIncidenceProjection diagram root coarser
              (IncidenceNode.vertex (Sum.inr
                (IncidenceNode.nonVerticialMap
                  (LevelSemiGraph diagram root finer)
                  (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition
                    diagram root refinement)
                  (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_isProper
                    diagram root refinement)
                  branch))) = _
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary,
            IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary]
          apply congrArg (fun value ↦ IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          rfl
  | edge edge => rfl
  | branch branch => rfl

/-- Every coarser faithful-incidence node has a finer lift.  First choose
any finer node over the same source node, then use Galois transitivity and
surjective automorphism descent to move its refinement to the prescribed
target. -/
theorem refinementIncidenceMap_surjective
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    Function.Surjective (RefinementIncidenceMap diagram root refinement) := by
  intro target
  obtain ⟨source, sourceOverTarget⟩ :=
    baseIncidenceProjection_surjective diagram root finer
      (BaseIncidenceProjection diagram root coarser target)
  have sameBase :
      BaseIncidenceProjection diagram root coarser
          (RefinementIncidenceMap diagram root refinement source) =
        BaseIncidenceProjection diagram root coarser target := by
    rw [baseIncidenceProjection_refinement diagram root refinement,
      sourceOverTarget]
  obtain ⟨targetAutomorphism, targetMoved⟩ :=
    incidenceEndpoint_automorphismOrbit diagram root coarser
      (RefinementIncidenceMap diagram root refinement source) target sameBase
  obtain ⟨sourceAutomorphism, automorphismMaps⟩ :=
    SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition_surjective
      diagram root refinement targetAutomorphism
  refine ⟨IncidenceNode.incidencePerm (LevelSemiGraph diagram root finer)
    finer.automorphismAction sourceAutomorphism source, ?_⟩
  rw [refinement_incidence_commutes diagram root refinement,
    automorphismMaps, targetMoved]

/-- Identity refinement induces the identity on faithful-incidence nodes. -/
@[simp]
theorem refinementIncidenceMap_id_apply
    (level :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (point : IncidenceNode (LevelSemiGraph diagram root level)) :
    RefinementIncidenceMap diagram root (𝟙 level) point = point := by
  cases point with
  | vertex point =>
      cases point with
      | inl vertex =>
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_original]
          exact congrArg (fun value ↦ IncidenceNode.vertex (Sum.inl value))
            (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_vertex_id
              diagram root level vertex)
      | inr branch =>
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary]
          apply congrArg (fun value ↦ IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          rcases branch with ⟨⟨edge, branch⟩, nonVerticial⟩
          apply Sigma.ext
          · exact SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_edge_id
              diagram root level edge
          · rfl
  | edge edge =>
      rw [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge]
      exact congrArg IncidenceNode.edge
        (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_edge_id
          diagram root level edge)
  | branch branch =>
      rw [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch]
      apply congrArg IncidenceNode.branch
      rcases branch with ⟨edge, branch⟩
      apply Sigma.ext
      · exact SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_edge_id
          diagram root level edge
      · rfl

/-- Composition of refinements is composition on faithful-incidence nodes. -/
theorem refinementIncidenceMap_comp_apply
    {first middle last :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last)
    (point : IncidenceNode (LevelSemiGraph diagram root first)) :
    RefinementIncidenceMap diagram root (firstMap ≫ secondMap) point =
      RefinementIncidenceMap diagram root secondMap
        (RefinementIncidenceMap diagram root firstMap point) := by
  cases point with
  | vertex point =>
      cases point with
      | inl vertex =>
          simp only [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_original]
          exact congrArg (fun value ↦ IncidenceNode.vertex (Sum.inl value))
            (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_vertex_comp
              diagram root firstMap secondMap vertex)
      | inr branch =>
          simp only [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary]
          apply congrArg (fun value ↦ IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          rcases branch with ⟨⟨edge, branch⟩, nonVerticial⟩
          apply Sigma.ext
          · exact SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_edge_comp
              diagram root firstMap secondMap edge
          · rfl
  | edge edge =>
      simp only [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge]
      exact congrArg IncidenceNode.edge
        (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_edge_comp
          diagram root firstMap secondMap edge)
  | branch branch =>
      simp only [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch]
      apply congrArg IncidenceNode.branch
      rcases branch with ⟨edge, branch⟩
      apply Sigma.ext
      · exact SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_edge_comp
          diagram root firstMap secondMap edge
      · rfl

/-- Canonical reduced-walk map under Galois-level refinement. -/
noncomputable def RefinementTreeMap
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    IncidenceTreeVertex diagram root finer →
      IncidenceTreeVertex diagram root coarser :=
  fun point ↦ UniversalVertex.castRoot
    (IncidenceGraph diagram root coarser)
    (refinementIncidenceMap_root diagram root refinement)
    (UniversalVertex.mapHom (IncidenceGraph diagram root finer)
      (IncidenceRoot diagram root finer)
      (IncidenceGraph diagram root coarser)
      (RefinementIncidenceMap diagram root refinement) point)

@[simp]
theorem refinementTreeMap_endpoint
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (point : IncidenceTreeVertex diagram root finer) :
    (RefinementTreeMap diagram root refinement point).endpoint =
      RefinementIncidenceMap diagram root refinement point.endpoint :=
  by
    unfold RefinementTreeMap
    rw [UniversalVertex.castRoot_endpoint,
      UniversalVertex.mapHom_endpoint]

@[simp]
theorem refinementTreeMap_base
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    RefinementTreeMap diagram root refinement
        (UniversalVertex.base (IncidenceGraph diagram root finer)
          (IncidenceRoot diagram root finer)) =
      UniversalVertex.base (IncidenceGraph diagram root coarser)
        (IncidenceRoot diagram root coarser) := by
  unfold RefinementTreeMap
  rw [UniversalVertex.mapHom_base, UniversalVertex.castRoot_base]

theorem refinementTreeMap_adj
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    {first second : IncidenceTreeVertex diagram root finer}
    (adjacent : (UniversalVertex.tree (IncidenceGraph diagram root finer)
      (IncidenceRoot diagram root finer)).Adj first second) :
    (UniversalVertex.tree (IncidenceGraph diagram root coarser)
      (IncidenceRoot diagram root coarser)).Adj
        (RefinementTreeMap diagram root refinement first)
        (RefinementTreeMap diagram root refinement second) :=
  by
    unfold RefinementTreeMap
    apply UniversalVertex.castRoot_adj
    exact UniversalVertex.mapHom_adj _ _ _ _ adjacent

/-- Identity refinement acts identically on the universal incidence tree. -/
@[simp]
theorem refinementTreeMap_id
    (level :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root) :
    RefinementTreeMap diagram root (𝟙 level) = id := by
  let graph := IncidenceGraph diagram root level
  let base := IncidenceRoot diagram root level
  apply UniversalVertex.map_eq_of_endpoint_eq_adj
    graph base graph base (RefinementTreeMap diagram root (𝟙 level)) id
    (point := UniversalVertex.base graph base)
  · intro point
    change (RefinementTreeMap diagram root (𝟙 level) point).endpoint =
      point.endpoint
    rw [refinementTreeMap_endpoint, refinementIncidenceMap_id_apply]
  · intro point neighbor adjacent
    exact refinementTreeMap_adj diagram root (𝟙 level) adjacent
  · intro point neighbor adjacent
    exact adjacent
  · simp [graph, base]

/-- Refinement maps of universal incidence trees respect composition. -/
theorem refinementTreeMap_comp
    {first middle last :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last) :
    RefinementTreeMap diagram root (firstMap ≫ secondMap) =
      RefinementTreeMap diagram root secondMap ∘
        RefinementTreeMap diagram root firstMap := by
  let sourceGraph := IncidenceGraph diagram root first
  let sourceRoot := IncidenceRoot diagram root first
  let targetGraph := IncidenceGraph diagram root last
  let targetRoot := IncidenceRoot diagram root last
  apply UniversalVertex.map_eq_of_endpoint_eq_adj
    sourceGraph sourceRoot targetGraph targetRoot
    (RefinementTreeMap diagram root (firstMap ≫ secondMap))
    (RefinementTreeMap diagram root secondMap ∘
      RefinementTreeMap diagram root firstMap)
    (point := UniversalVertex.base sourceGraph sourceRoot)
  · intro point
    change (RefinementTreeMap diagram root (firstMap ≫ secondMap) point).endpoint =
      (RefinementTreeMap diagram root secondMap
        (RefinementTreeMap diagram root firstMap point)).endpoint
    rw [refinementTreeMap_endpoint, refinementTreeMap_endpoint,
      refinementTreeMap_endpoint]
    exact refinementIncidenceMap_comp_apply diagram root firstMap secondMap
      point.endpoint
  · intro point neighbor adjacent
    exact refinementTreeMap_adj diagram root (firstMap ≫ secondMap) adjacent
  · intro point neighbor adjacent
    exact refinementTreeMap_adj diagram root secondMap
      (refinementTreeMap_adj diagram root firstMap adjacent)
  · simp [sourceGraph, sourceRoot]

/-- The finite Galois symmetry descended along a pointed refinement. -/
noncomputable def TransitionedSymmetry
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer) : Aut coarser.object :=
  SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition
    diagram root refinement
    (UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation)

/-- Image of the transformed finer base point in the coarser universal
tree. -/
noncomputable def TransitionedBaseImage
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer) :
    IncidenceTreeVertex diagram root coarser :=
  RefinementTreeMap diagram root refinement <|
    UniversalVertex.CompositeDeckTransformation.treePerm transformation <|
      UniversalVertex.base (IncidenceGraph diagram root finer)
        (IncidenceRoot diagram root finer)

/-- The descended symmetry carries the coarser root to the endpoint selected
by the transformed finer base point. -/
theorem transitionedBaseImage_endpoint
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer) :
    (IncidenceActionHom diagram root coarser
      (TransitionedSymmetry diagram root refinement transformation)).1
        (IncidenceRoot diagram root coarser) =
      (TransitionedBaseImage diagram root refinement transformation).endpoint := by
  rw [TransitionedBaseImage, refinementTreeMap_endpoint,
    UniversalVertex.CompositeDeckTransformation.endpoint_apply]
  change IncidenceNode.incidencePerm (LevelSemiGraph diagram root coarser)
      coarser.automorphismAction
        (TransitionedSymmetry diagram root refinement transformation)
        (IncidenceRoot diagram root coarser) =
    RefinementIncidenceMap diagram root refinement
      (IncidenceNode.incidencePerm (LevelSemiGraph diagram root finer)
        finer.automorphismAction
          (UniversalVertex.CompositeDeckTransformation.baseSymmetry
            transformation)
          (IncidenceRoot diagram root finer))
  rw [← refinementIncidenceMap_root diagram root refinement]
  exact (refinement_incidence_commutes diagram root refinement
    (UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation)
    (IncidenceRoot diagram root finer)).symm

/-- Transition a complete composite deck transformation by its descended
finite symmetry and the image of one base point. -/
noncomputable def deckTransitionToFun
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer) :
    DeckGroup diagram root coarser :=
  UniversalVertex.CompositeDeckTransformation.between
    (TransitionedSymmetry diagram root refinement transformation)
    (UniversalVertex.base (IncidenceGraph diagram root coarser)
      (IncidenceRoot diagram root coarser))
    (TransitionedBaseImage diagram root refinement transformation)
    (transitionedBaseImage_endpoint diagram root refinement transformation)

@[simp]
theorem deckTransitionToFun_baseSymmetry
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer) :
    UniversalVertex.CompositeDeckTransformation.baseSymmetry
        (deckTransitionToFun diagram root refinement transformation) =
      TransitionedSymmetry diagram root refinement transformation :=
  rfl

@[simp]
theorem deckTransitionToFun_base
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer) :
    UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransitionToFun diagram root refinement transformation)
        (UniversalVertex.base (IncidenceGraph diagram root coarser)
          (IncidenceRoot diagram root coarser)) =
      TransitionedBaseImage diagram root refinement transformation :=
  UniversalVertex.CompositeDeckTransformation.between_apply_first _ _ _ _

/-- The transitioned deck transformation is the unique lift commuting with
the canonical refinement map of universal trees. -/
theorem deckTransitionToFun_commutes
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer)
    (point : IncidenceTreeVertex diagram root finer) :
    RefinementTreeMap diagram root refinement
        (UniversalVertex.CompositeDeckTransformation.treePerm
          transformation point) =
      UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransitionToFun diagram root refinement transformation)
        (RefinementTreeMap diagram root refinement point) := by
  let sourceGraph := IncidenceGraph diagram root finer
  let sourceRoot := IncidenceRoot diagram root finer
  let targetGraph := IncidenceGraph diagram root coarser
  let targetRoot := IncidenceRoot diagram root coarser
  let first : UniversalVertex sourceGraph sourceRoot →
      UniversalVertex targetGraph targetRoot :=
    fun value ↦ RefinementTreeMap diagram root refinement <|
      UniversalVertex.CompositeDeckTransformation.treePerm transformation value
  let second : UniversalVertex sourceGraph sourceRoot →
      UniversalVertex targetGraph targetRoot :=
    fun value ↦ UniversalVertex.CompositeDeckTransformation.treePerm
      (deckTransitionToFun diagram root refinement transformation)
      (RefinementTreeMap diagram root refinement value)
  have endpointEquality : ∀ value, (first value).endpoint =
      (second value).endpoint := by
    intro value
    change (RefinementTreeMap diagram root refinement
        (UniversalVertex.CompositeDeckTransformation.treePerm
          transformation value)).endpoint =
      (UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransitionToFun diagram root refinement transformation)
        (RefinementTreeMap diagram root refinement value)).endpoint
    rw [refinementTreeMap_endpoint]
    rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply
      transformation]
    rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply
      (deckTransitionToFun diagram root refinement transformation)]
    rw [refinementTreeMap_endpoint]
    rw [deckTransitionToFun_baseSymmetry]
    change RefinementIncidenceMap diagram root refinement
        (IncidenceNode.incidencePerm (LevelSemiGraph diagram root finer)
          finer.automorphismAction
            (UniversalVertex.CompositeDeckTransformation.baseSymmetry
              transformation) value.endpoint) =
      IncidenceNode.incidencePerm (LevelSemiGraph diagram root coarser)
        coarser.automorphismAction
          (TransitionedSymmetry diagram root refinement transformation)
          (RefinementIncidenceMap diagram root refinement value.endpoint)
    exact refinement_incidence_commutes diagram root refinement _ _
  have firstAdjacent : ∀ {value neighbor},
      (UniversalVertex.tree sourceGraph sourceRoot).Adj value neighbor →
        (UniversalVertex.tree targetGraph targetRoot).Adj
          (first value) (first neighbor) := by
    intro value neighbor adjacent
    apply refinementTreeMap_adj diagram root refinement
    exact (UniversalVertex.CompositeDeckTransformation.adjacency_apply_iff
      transformation value neighbor).mpr adjacent
  have secondAdjacent : ∀ {value neighbor},
      (UniversalVertex.tree sourceGraph sourceRoot).Adj value neighbor →
        (UniversalVertex.tree targetGraph targetRoot).Adj
          (second value) (second neighbor) := by
    intro value neighbor adjacent
    exact (UniversalVertex.CompositeDeckTransformation.adjacency_apply_iff
      (deckTransitionToFun diagram root refinement transformation)
      _ _).mpr (refinementTreeMap_adj diagram root refinement adjacent)
  have atBase : first (UniversalVertex.base sourceGraph sourceRoot) =
      second (UniversalVertex.base sourceGraph sourceRoot) := by
    change RefinementTreeMap diagram root refinement
        (UniversalVertex.CompositeDeckTransformation.treePerm transformation
          (UniversalVertex.base sourceGraph sourceRoot)) =
      UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransitionToFun diagram root refinement transformation)
        (RefinementTreeMap diagram root refinement
          (UniversalVertex.base sourceGraph sourceRoot))
    rw [refinementTreeMap_base, deckTransitionToFun_base]
    rfl
  have mapEquality := UniversalVertex.map_eq_of_endpoint_eq_adj
    sourceGraph sourceRoot targetGraph targetRoot first second
      endpointEquality firstAdjacent secondAdjacent
      (UniversalVertex.base sourceGraph sourceRoot) atBase
  exact congrFun mapEquality point

/-- The refinement transition of complete composite deck groups.  Both the
finite Galois symmetry and its lifted tree permutation are derived from the
pointed morphism of Galois levels. -/
noncomputable def deckTransition
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    DeckGroup diagram root finer →* DeckGroup diagram root coarser where
  toFun := deckTransitionToFun diagram root refinement
  map_one' := by
    apply UniversalVertex.CompositeDeckTransformation.encoding_injective
      (UniversalVertex.base (IncidenceGraph diagram root coarser)
        (IncidenceRoot diagram root coarser))
    apply Prod.ext
    · change TransitionedSymmetry diagram root refinement 1 = 1
      change (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition
        diagram root refinement) 1 = 1
      exact map_one _
    · change UniversalVertex.CompositeDeckTransformation.treePerm
          (deckTransitionToFun diagram root refinement 1)
          (UniversalVertex.base (IncidenceGraph diagram root coarser)
            (IncidenceRoot diagram root coarser)) =
        UniversalVertex.base (IncidenceGraph diagram root coarser)
          (IncidenceRoot diagram root coarser)
      rw [deckTransitionToFun_base, TransitionedBaseImage]
      change RefinementTreeMap diagram root refinement
          (UniversalVertex.base (IncidenceGraph diagram root finer)
            (IncidenceRoot diagram root finer)) = _
      exact refinementTreeMap_base diagram root refinement
  map_mul' first second := by
    apply UniversalVertex.CompositeDeckTransformation.encoding_injective
      (UniversalVertex.base (IncidenceGraph diagram root coarser)
        (IncidenceRoot diagram root coarser))
    apply Prod.ext
    · change TransitionedSymmetry diagram root refinement (first * second) =
        TransitionedSymmetry diagram root refinement first *
          TransitionedSymmetry diagram root refinement second
      change (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition
          diagram root refinement)
            (UniversalVertex.CompositeDeckTransformation.baseSymmetry first *
              UniversalVertex.CompositeDeckTransformation.baseSymmetry second) =
        _
      exact map_mul _ _ _
    · change UniversalVertex.CompositeDeckTransformation.treePerm
          (deckTransitionToFun diagram root refinement (first * second))
          (UniversalVertex.base (IncidenceGraph diagram root coarser)
            (IncidenceRoot diagram root coarser)) =
        UniversalVertex.CompositeDeckTransformation.treePerm
          (deckTransitionToFun diagram root refinement first)
          (UniversalVertex.CompositeDeckTransformation.treePerm
            (deckTransitionToFun diagram root refinement second)
            (UniversalVertex.base (IncidenceGraph diagram root coarser)
              (IncidenceRoot diagram root coarser)))
      rw [deckTransitionToFun_base, TransitionedBaseImage]
      change RefinementTreeMap diagram root refinement
          (UniversalVertex.CompositeDeckTransformation.treePerm first
            (UniversalVertex.CompositeDeckTransformation.treePerm second
              (UniversalVertex.base (IncidenceGraph diagram root finer)
                (IncidenceRoot diagram root finer)))) =
        UniversalVertex.CompositeDeckTransformation.treePerm
          (deckTransitionToFun diagram root refinement first)
          (UniversalVertex.CompositeDeckTransformation.treePerm
            (deckTransitionToFun diagram root refinement second)
            (UniversalVertex.base (IncidenceGraph diagram root coarser)
              (IncidenceRoot diagram root coarser)))
      rw [deckTransitionToFun_base, TransitionedBaseImage]
      exact deckTransitionToFun_commutes diagram root refinement first _

@[simp]
theorem deckTransition_apply
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer) :
    deckTransition diagram root refinement transformation =
      deckTransitionToFun diagram root refinement transformation :=
  rfl

/-- Identity refinement induces the identity deck-group homomorphism. -/
@[simp]
theorem deckTransition_id
    (level :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root) :
    deckTransition diagram root (𝟙 level) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro transformation
  apply UniversalVertex.CompositeDeckTransformation.encoding_injective
    (UniversalVertex.base (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level))
  apply Prod.ext
  · change SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition
        diagram root (𝟙 level)
          (UniversalVertex.CompositeDeckTransformation.baseSymmetry
            transformation) =
      UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation
    simp [SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition]
  · change UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransitionToFun diagram root (𝟙 level) transformation)
        (UniversalVertex.base (IncidenceGraph diagram root level)
          (IncidenceRoot diagram root level)) =
      UniversalVertex.CompositeDeckTransformation.treePerm transformation
        (UniversalVertex.base (IncidenceGraph diagram root level)
          (IncidenceRoot diagram root level))
    rw [deckTransitionToFun_base,
      TransitionedBaseImage, refinementTreeMap_id]
    rfl

/-- Deck-group transitions respect composition of pointed refinements. -/
theorem deckTransition_comp
    {first middle last :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last) :
    deckTransition diagram root (firstMap ≫ secondMap) =
      (deckTransition diagram root secondMap).comp
        (deckTransition diagram root firstMap) := by
  apply MonoidHom.ext
  intro transformation
  apply UniversalVertex.CompositeDeckTransformation.encoding_injective
    (UniversalVertex.base (IncidenceGraph diagram root last)
      (IncidenceRoot diagram root last))
  apply Prod.ext
  · change SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition
        diagram root (firstMap ≫ secondMap)
          (UniversalVertex.CompositeDeckTransformation.baseSymmetry
            transformation) =
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition
        diagram root secondMap
          (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.automorphismTransition
            diagram root firstMap
              (UniversalVertex.CompositeDeckTransformation.baseSymmetry
                transformation))
    letI : GaloisCategory diagram.GluedObject :=
      SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
    letI : PreGaloisCategory.FiberFunctor
        (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root) :=
      SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
    letI : PreGaloisCategory.IsGalois first.object := first.isGalois
    letI : PreGaloisCategory.IsGalois middle.object := middle.isGalois
    letI : PreGaloisCategory.IsGalois last.object := last.isGalois
    change PreGaloisCategory.autMap (firstMap.val ≫ secondMap.val)
        (UniversalVertex.CompositeDeckTransformation.baseSymmetry
          transformation) = _
    rw [PreGaloisCategory.autMap_comp]
    rfl
  · change UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransitionToFun diagram root (firstMap ≫ secondMap) transformation)
        (UniversalVertex.base (IncidenceGraph diagram root last)
          (IncidenceRoot diagram root last)) =
      UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransitionToFun diagram root secondMap
          (deckTransitionToFun diagram root firstMap transformation))
        (UniversalVertex.base (IncidenceGraph diagram root last)
          (IncidenceRoot diagram root last))
    rw [deckTransitionToFun_base, TransitionedBaseImage,
      deckTransitionToFun_base, TransitionedBaseImage,
      deckTransitionToFun_base, TransitionedBaseImage]
    exact congrFun (refinementTreeMap_comp diagram root firstMap secondMap)
      (UniversalVertex.CompositeDeckTransformation.treePerm transformation
        (UniversalVertex.base (IncidenceGraph diagram root first)
          (IncidenceRoot diagram root first)))

end

end SourceGaloisCombinatorialUniversalCover

namespace SourceIsolatedGaloisCombinatorialUniversalCover

noncomputable section

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (noVertex : ¬Nonempty diagram.base.Vertex)
    (level : diagram.IsolatedGaloisLevel noVertex)

local instance isolatedCoverCategory :
    Category (SourceSemiGraphOfAnabelioids.isolatedAnabelioid
      diagram noVertex).Cover :=
  (SourceSemiGraphOfAnabelioids.isolatedAnabelioid
    diagram noVertex).coverCategory

local instance isolatedGaloisCategory :
    GaloisCategory (SourceSemiGraphOfAnabelioids.isolatedAnabelioid
      diagram noVertex).Cover :=
  (SourceSemiGraphOfAnabelioids.isolatedAnabelioid
    diagram noVertex).galoisCategory

local instance isolatedFiberFunctor :
    PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.isolatedAnabelioid
        diagram noVertex).fiber :=
  (SourceSemiGraphOfAnabelioids.isolatedAnabelioid
    diagram noVertex).fiberFunctor

/-- For the unique isolated edge, the connected finite level is already its
own combinatorial universal cover. -/
abbrev Cover : SourceSemiGraph.{u} :=
  level.semiGraph

/-- The identity projection to the isolated finite level. -/
def projection :
    (Cover diagram noVertex level).Hom level.semiGraph :=
  SourceSemiGraph.Hom.id level.semiGraph

/-- The complete composite deck group is the full Galois automorphism group;
it must not be replaced by its trivial visible incidence image. -/
abbrev DeckGroup := Aut level.object

/-- The level's fiber is the faithful realization of its constituent cover. -/
abbrev FaithfulRealization :=
  (SourceSemiGraphOfAnabelioids.isolatedAnabelioid diagram noVertex).fiber.obj
    level.object

/-- The full isolated-edge deck action is faithful on constituent fiber
data, even when its incidence action is trivial. -/
theorem deckAction_faithful :
    FaithfulSMul (DeckGroup diagram noVertex level)
      (FaithfulRealization diagram noVertex level) := by
  let data := SourceSemiGraphOfAnabelioids.isolatedAnabelioid diagram noVertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  constructor
  intro first second actionEquality
  apply PreGaloisCategory.evaluation_aut_injective_of_isConnected
    data.fiber level.object level.point
  exact actionEquality level.point

/-- Isolated finite-level deck groups are finite, hence countable. -/
theorem deckGroup_countable :
    Countable (DeckGroup diagram noVertex level) := by
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  exact Finite.to_countable

/-- The full isolated-edge deck group carries the discrete topology. -/
instance deckGroupTopologicalSpace :
    TopologicalSpace (DeckGroup diagram noVertex level) := ⊥

instance deckGroupDiscreteTopology :
    DiscreteTopology (DeckGroup diagram noVertex level) :=
  discreteTopology_bot _

/-- Refinement produces the full surjective group transition constructed in
#55. -/
noncomputable def deckTransition
    {finer coarser : diagram.IsolatedGaloisLevel noVertex}
    (refinement : finer ⟶ coarser) :
    DeckGroup diagram noVertex finer →*
      DeckGroup diagram noVertex coarser :=
  SourceSemiGraphOfAnabelioids.IsolatedGaloisLevel.automorphismTransition
    diagram noVertex refinement

theorem deckTransition_surjective
    {finer coarser : diagram.IsolatedGaloisLevel noVertex}
    (refinement : finer ⟶ coarser) :
    Function.Surjective (deckTransition diagram noVertex refinement) :=
  SourceSemiGraphOfAnabelioids.IsolatedGaloisLevel.automorphismTransition_surjective
    diagram noVertex refinement

/-- Identity refinement induces the identity isolated deck transition. -/
@[simp]
theorem isolatedDeckTransition_id
    (level : diagram.IsolatedGaloisLevel noVertex) :
    deckTransition diagram noVertex (𝟙 level) = MonoidHom.id _ := by
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  apply MonoidHom.ext
  intro transformation
  change PreGaloisCategory.autMap (𝟙 level.object) transformation =
    transformation
  simp

/-- Isolated deck transitions respect composition of refinements. -/
theorem isolatedDeckTransition_comp
    {first middle last : diagram.IsolatedGaloisLevel noVertex}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last) :
    deckTransition diagram noVertex (firstMap ≫ secondMap) =
      (deckTransition diagram noVertex secondMap).comp
        (deckTransition diagram noVertex firstMap) := by
  letI : PreGaloisCategory.IsGalois first.object := first.isGalois
  letI : PreGaloisCategory.IsGalois middle.object := middle.isGalois
  letI : PreGaloisCategory.IsGalois last.object := last.isGalois
  apply MonoidHom.ext
  intro transformation
  change PreGaloisCategory.autMap (firstMap.val ≫ secondMap.val)
      transformation =
    PreGaloisCategory.autMap secondMap.val
      (PreGaloisCategory.autMap firstMap.val transformation)
  rw [PreGaloisCategory.autMap_comp]
  rfl

end

end SourceIsolatedGaloisCombinatorialUniversalCover

namespace SourceRawNormalOpenCombinatorialUniversalCover

open SourceCombinatorialUniversalCover

variable {Ambient : Type u} [Group Ambient] [TopologicalSpace Ambient]
    (diagram : SourceSemiGraphSubgroupDiagram.{u} Ambient)
    (level : OpenNormalSubgroup Ambient)
    (root : (diagram.normalOpenLevelSemiGraph level).Vertex)

/-- The normal-open finite semi-graph at the selected level. -/
abbrev LevelSemiGraph : SourceSemiGraph :=
  diagram.normalOpenLevelSemiGraph level

/-- The actual combinatorial universal cover at a normal-open level. -/
noncomputable abbrev Cover : SourceSemiGraph :=
  SourceSemiGraphUniversalCover.semiGraphCover
    (LevelSemiGraph diagram level) root

/-- Projection from the normal-open combinatorial universal cover to its
finite coset level. -/
noncomputable abbrev projection :
    (Cover diagram level root).Hom (LevelSemiGraph diagram level) :=
  SourceSemiGraphUniversalCover.projection
    (LevelSemiGraph diagram level) root

/-- The normal-open universal-cover projection is a proper excision. -/
theorem projection_isGraphCovering :
    (projection diagram level root).IsGraphCovering :=
  SourceSemiGraphUniversalCover.projection_isGraphCovering
    (LevelSemiGraph diagram level) root

/-- Faithful incidence graph of the compactified normal-open level. -/
abbrev IncidenceGraph :=
  IncidenceNode.incidenceGraph (LevelSemiGraph diagram level)

/-- Root node in the normal-open incidence graph. -/
abbrev IncidenceRoot : IncidenceNode (LevelSemiGraph diagram level) :=
  IncidenceNode.vertex (Sum.inl root)

/-- The source incidence graph underneath every normal-open level. -/
abbrev BaseIncidenceGraph :=
  IncidenceNode.incidenceGraph diagram.base

/-- Canonical faithful-incidence projection from a normal-open level to the
source semi-graph. -/
noncomputable abbrev BaseIncidenceProjection :
    IncidenceGraph diagram level →g BaseIncidenceGraph diagram :=
  IncidenceNode.properIncidenceGraphHom (LevelSemiGraph diagram level)
    (diagram.normalOpenLevelProjection level)
    (diagram.normalOpenLevelProjection_isProper level)

@[simp]
theorem baseIncidenceProjection_vertex_original
    (vertex : (LevelSemiGraph diagram level).Vertex) :
    BaseIncidenceProjection diagram level
        (IncidenceNode.vertex (Sum.inl vertex)) =
      IncidenceNode.vertex (Sum.inl vertex.1) :=
  rfl

@[simp]
theorem baseIncidenceProjection_vertex_boundary
    (branch : (LevelSemiGraph diagram level).NonVerticialBranch) :
    BaseIncidenceProjection diagram level
        (IncidenceNode.vertex (Sum.inr branch)) =
      IncidenceNode.vertex (Sum.inr
        (IncidenceNode.nonVerticialMap (LevelSemiGraph diagram level)
          (diagram.normalOpenLevelProjection level)
          (diagram.normalOpenLevelProjection_isProper level) branch)) :=
  rfl

@[simp]
theorem baseIncidenceProjection_edge
    (edge : (LevelSemiGraph diagram level).Edge) :
    BaseIncidenceProjection diagram level (IncidenceNode.edge edge) =
      IncidenceNode.edge edge.1 :=
  rfl

@[simp]
theorem baseIncidenceProjection_branch
    (branch : (LevelSemiGraph diagram level).TotalBranch) :
    BaseIncidenceProjection diagram level (IncidenceNode.branch branch) =
      IncidenceNode.branch
        ((diagram.normalOpenLevelProjection level).totalBranchMap branch) :=
  rfl

/-- Universal incidence tree of the selected normal-open level. -/
abbrev IncidenceTreeVertex :=
  UniversalVertex (IncidenceGraph diagram level)
    (IncidenceRoot diagram level root)

/-- Endpoint of the composite universal cover over the source incidence
graph. -/
noncomputable def compositeEndpoint
    (point : IncidenceTreeVertex diagram level root) :
    IncidenceNode diagram.base :=
  BaseIncidenceProjection diagram level point.endpoint

/-- A fiber of the composite universal cover over a source incidence node. -/
abbrev CompositeFiber (basePoint : IncidenceNode diagram.base) :=
  {point : IncidenceTreeVertex diagram level root //
    compositeEndpoint diagram level root point = basePoint}

/-- The compactified normal-open universal cover is connected and acyclic. -/
theorem incidenceTree_isTree :
    (UniversalVertex.tree (IncidenceGraph diagram level)
      (IncidenceRoot diagram level root)).IsTree :=
  UniversalVertex.tree_isTree (IncidenceGraph diagram level)
    (IncidenceRoot diagram level root)

/-- Vertical deck group of the universal cover over the selected finite
normal-open level. -/
abbrev VerticalDeckGroup :=
  UniversalVertex.DeckTransformation (IncidenceGraph diagram level)
    (IncidenceRoot diagram level root)

/-- Ambient action on the faithful incidence graph of a normal-open level. -/
abbrev IncidenceActionHom :=
  UniversalVertex.incidenceAutomorphismHom
    (diagram.normalOpenLevel level).cosetAction

/-- The finite group of incidence-graph symmetries induced by the ambient
fundamental group at this normal-open level. -/
abbrev LevelSymmetries : Subgroup
    (UniversalVertex.graphAutomorphismSubgroup
      (IncidenceGraph diagram level)) :=
  (IncidenceActionHom diagram level).range

/-- Deck group of the composite universal cover over the source semi-graph:
tree automorphisms lying over the ambient finite-level symmetries. -/
abbrev DeckGroup :=
  UniversalVertex.LiftedDeckTransformation
    (IncidenceGraph diagram level) (IncidenceRoot diagram level root)
      (LevelSymmetries diagram level)

/-- The normal-open deck group acts faithfully on the complete universal
incidence tree. -/
theorem deckAction_faithful :
    FaithfulSMul (DeckGroup diagram level root)
      (IncidenceTreeVertex diagram level root) :=
  UniversalVertex.LiftedDeckTransformation.faithful_action

/-- The normal-open deck action is transitive on every nonempty incidence
fiber. -/
theorem deckAction_transitive
    (first second : IncidenceTreeVertex diagram level root)
    (sameEndpoint : first.endpoint = second.endpoint) :
    ∃ transformation : DeckGroup diagram level root,
      transformation.1 first = second := by
  apply UniversalVertex.LiftedDeckTransformation.exists_apply_eq
  refine ⟨1, ?_⟩
  simpa using sameEndpoint

/-- The ambient coset action is transitive on every fiber of the
normal-open faithful-incidence projection. -/
theorem incidenceEndpoint_ambientOrbit
    (first second : IncidenceNode (LevelSemiGraph diagram level))
    (sameBase : BaseIncidenceProjection diagram level first =
      BaseIncidenceProjection diagram level second) :
    ∃ element : Ambient,
      IncidenceNode.incidencePerm (LevelSemiGraph diagram level)
          (diagram.normalOpenLevel level).cosetAction element first = second := by
  cases first with
  | vertex first =>
      cases second with
      | vertex second =>
          cases first with
          | inl first =>
              cases second with
              | inl second =>
                  rcases first with ⟨vertex, firstCoset⟩
                  rcases second with ⟨secondVertex, secondCoset⟩
                  simp only [baseIncidenceProjection_vertex_original] at sameBase
                  have vertexEquality : vertex = secondVertex := by
                    exact Sum.inl.inj (IncidenceNode.vertex.inj sameBase)
                  subst secondVertex
                  obtain ⟨element, cosetEquality⟩ :=
                    MulAction.exists_smul_eq Ambient firstCoset secondCoset
                  refine ⟨element, ?_⟩
                  rw [IncidenceNode.incidencePerm_vertex]
                  apply congrArg (fun value =>
                    IncidenceNode.vertex (Sum.inl value))
                  exact Sigma.ext rfl (heq_of_eq cosetEquality)
              | inr second =>
                  simp only [baseIncidenceProjection_vertex_original,
                    baseIncidenceProjection_vertex_boundary] at sameBase
                  have impossible := IncidenceNode.vertex.inj sameBase
                  cases impossible
          | inr first =>
              cases second with
              | inl second =>
                  simp only [baseIncidenceProjection_vertex_original,
                    baseIncidenceProjection_vertex_boundary] at sameBase
                  have impossible := IncidenceNode.vertex.inj sameBase
                  cases impossible
              | inr second =>
                  rcases first with
                    ⟨⟨⟨edge, firstCoset⟩, branch⟩, firstNone⟩
                  rcases second with
                    ⟨⟨⟨secondEdge, secondCoset⟩, secondBranch⟩,
                      secondNone⟩
                  simp only [baseIncidenceProjection_vertex_boundary] at sameBase
                  have branchEquality :
                      (⟨edge, branch⟩ : diagram.base.TotalBranch) =
                        ⟨secondEdge, secondBranch⟩ := by
                    exact congrArg Subtype.val <|
                      Sum.inr.inj (IncidenceNode.vertex.inj sameBase)
                  cases branchEquality
                  obtain ⟨element, cosetEquality⟩ :=
                    MulAction.exists_smul_eq Ambient firstCoset secondCoset
                  refine ⟨element, ?_⟩
                  rw [IncidenceNode.incidencePerm_vertex]
                  apply congrArg (fun value =>
                    IncidenceNode.vertex (Sum.inr value))
                  apply Subtype.ext
                  apply Sigma.ext
                  · exact Sigma.ext rfl (heq_of_eq cosetEquality)
                  · rfl
      | edge second =>
          simp only [baseIncidenceProjection_edge] at sameBase
          cases sameBase
      | branch second =>
          simp only [baseIncidenceProjection_branch] at sameBase
          cases sameBase
  | edge first =>
      cases second with
      | vertex second =>
          simp only [baseIncidenceProjection_edge] at sameBase
          cases sameBase
      | edge second =>
          rcases first with ⟨edge, firstCoset⟩
          rcases second with ⟨secondEdge, secondCoset⟩
          simp only [baseIncidenceProjection_edge] at sameBase
          have edgeEquality : edge = secondEdge :=
            IncidenceNode.edge.inj sameBase
          subst secondEdge
          obtain ⟨element, cosetEquality⟩ :=
            MulAction.exists_smul_eq Ambient firstCoset secondCoset
          refine ⟨element, ?_⟩
          rw [IncidenceNode.incidencePerm_edge]
          apply congrArg IncidenceNode.edge
          exact Sigma.ext rfl (heq_of_eq cosetEquality)
      | branch second =>
          simp only [baseIncidenceProjection_edge,
            baseIncidenceProjection_branch] at sameBase
          cases sameBase
  | branch first =>
      cases second with
      | vertex second =>
          simp only [baseIncidenceProjection_branch] at sameBase
          cases sameBase
      | edge second =>
          simp only [baseIncidenceProjection_edge,
            baseIncidenceProjection_branch] at sameBase
          cases sameBase
      | branch second =>
          rcases first with ⟨⟨edge, firstCoset⟩, branch⟩
          rcases second with ⟨⟨secondEdge, secondCoset⟩, secondBranch⟩
          simp only [baseIncidenceProjection_branch] at sameBase
          have branchEquality :
              (⟨edge, branch⟩ : diagram.base.TotalBranch) =
                ⟨secondEdge, secondBranch⟩ :=
            IncidenceNode.branch.inj sameBase
          cases branchEquality
          obtain ⟨element, cosetEquality⟩ :=
            MulAction.exists_smul_eq Ambient firstCoset secondCoset
          refine ⟨element, ?_⟩
          rw [IncidenceNode.incidencePerm_branch]
          apply congrArg IncidenceNode.branch
          apply Sigma.ext
          · exact Sigma.ext rfl (heq_of_eq cosetEquality)
          · rfl

/-- The ambient action changes only coset coordinates, hence is over the
source incidence graph. -/
theorem baseIncidenceProjection_incidencePerm
    (element : Ambient)
    (point : IncidenceNode (LevelSemiGraph diagram level)) :
    BaseIncidenceProjection diagram level
        (IncidenceNode.incidencePerm (LevelSemiGraph diagram level)
          (diagram.normalOpenLevel level).cosetAction element point) =
      BaseIncidenceProjection diagram level point := by
  cases point with
  | vertex point =>
      cases point with
      | inl vertex => rfl
      | inr branch =>
          rw [IncidenceNode.incidencePerm_vertex]
          change BaseIncidenceProjection diagram level
              (IncidenceNode.vertex (Sum.inr
                (IncidenceNode.nonVerticialBranchPerm
                  (LevelSemiGraph diagram level)
                  (diagram.normalOpenLevel level).cosetAction element branch))) = _
          rw [
            baseIncidenceProjection_vertex_boundary,
            baseIncidenceProjection_vertex_boundary]
          apply congrArg (fun value => IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          rfl
  | edge edge => rfl
  | branch branch => rfl

/-- More generally, two lifts in one orbit of the ambient finite-level action
are related by a composite deck transformation. -/
theorem deckAction_transitive_of_ambient
    (first second : IncidenceTreeVertex diagram level root)
    (sameOrbit : ∃ element : Ambient,
      IncidenceNode.incidencePerm (LevelSemiGraph diagram level)
          (diagram.normalOpenLevel level).cosetAction element first.endpoint =
        second.endpoint) :
    ∃ transformation : DeckGroup diagram level root,
      transformation.1 first = second := by
  obtain ⟨element, endpointEquality⟩ := sameOrbit
  apply UniversalVertex.LiftedDeckTransformation.exists_apply_eq
  refine ⟨⟨(IncidenceActionHom diagram level) element,
    ⟨element, rfl⟩⟩, ?_⟩
  exact endpointEquality

/-- Every composite deck transformation preserves the endpoint in the source
incidence graph. -/
theorem compositeEndpoint_deck_apply
    (transformation : DeckGroup diagram level root)
    (point : IncidenceTreeVertex diagram level root) :
    compositeEndpoint diagram level root (transformation.1 point) =
      compositeEndpoint diagram level root point := by
  obtain ⟨symmetry, endpointLaw⟩ := transformation.2.1
  obtain ⟨element, symmetryEquality⟩ := symmetry.2
  unfold compositeEndpoint
  rw [endpointLaw]
  have permutationEquality : symmetry.1.1 =
      IncidenceNode.incidencePerm (LevelSemiGraph diagram level)
        (diagram.normalOpenLevel level).cosetAction element := by
    exact congrArg Subtype.val symmetryEquality.symm
  rw [permutationEquality]
  exact baseIncidenceProjection_incidencePerm diagram level element point.endpoint

/-- The composite deck group is transitive on every nonempty fiber over the
source incidence graph. -/
theorem deckAction_transitive_compositeFiber
    (first second : IncidenceTreeVertex diagram level root)
    (sameFiber : compositeEndpoint diagram level root first =
      compositeEndpoint diagram level root second) :
    ∃ transformation : DeckGroup diagram level root,
      transformation.1 first = second :=
  deckAction_transitive_of_ambient diagram level root first second <|
    incidenceEndpoint_ambientOrbit diagram level first.endpoint second.endpoint
      sameFiber

/-- Under the paper's finite-base hypotheses, every normal-open deck group is
countable. -/
theorem deckGroup_countable
    [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    Countable (DeckGroup diagram level root) := by
  letI : Finite (LevelSemiGraph diagram level).Vertex :=
    diagram.normalOpenLevel_vertices_finite level
  letI : Finite (LevelSemiGraph diagram level).Edge :=
    diagram.normalOpenLevel_edges_finite level
  letI : Countable (LevelSemiGraph diagram level).Vertex := Finite.to_countable
  letI : Countable (LevelSemiGraph diagram level).Edge := Finite.to_countable
  letI : Finite (IncidenceNode (LevelSemiGraph diagram level)) := inferInstance
  letI : Finite (LevelSymmetries diagram level) := inferInstance
  letI : Countable (LevelSymmetries diagram level) := Finite.to_countable
  infer_instance

/-- The deck-group topology at each normal-open level is discrete. -/
theorem deckGroup_discreteTopology :
    DiscreteTopology (DeckGroup diagram level root) :=
  inferInstance

/-- Refinement of normal-open levels is already an equivariant proper
semi-graph morphism on the finite quotients. -/
theorem refinement_isProper
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) :
    (diagram.normalOpenLevelTransition refinement).IsProper :=
  diagram.normalOpenLevelTransition_isProper refinement

/-- Faithful-incidence map induced by refinement of normal-open levels. -/
noncomputable abbrev RefinementIncidenceMap
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) :
    IncidenceGraph diagram finer →g IncidenceGraph diagram coarser :=
  IncidenceNode.properIncidenceGraphHom (LevelSemiGraph diagram finer)
    (diagram.normalOpenLevelTransition refinement)
    (diagram.normalOpenLevelTransition_isProper refinement)

/-- Refinement commutes with the ambient action on vertices. -/
theorem refinement_vertex_commutes
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) (element : Ambient)
    (vertex : (diagram.normalOpenLevelSemiGraph finer).Vertex) :
    diagram.normalOpenLevelVertexMap refinement
        ((diagram.normalOpenLevel finer).cosetAction.vertexAction element vertex) =
      (diagram.normalOpenLevel coarser).cosetAction.vertexAction element
        (diagram.normalOpenLevelVertexMap refinement vertex) :=
  diagram.normalOpenLevelVertexMap_action refinement element vertex

/-- Refinement commutes with the ambient action on edges. -/
theorem refinement_edge_commutes
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) (element : Ambient)
    (edge : (diagram.normalOpenLevelSemiGraph finer).Edge) :
    diagram.normalOpenLevelEdgeMap refinement
        ((diagram.normalOpenLevel finer).cosetAction.edgeAction element edge) =
      (diagram.normalOpenLevel coarser).cosetAction.edgeAction element
        (diagram.normalOpenLevelEdgeMap refinement edge) :=
  diagram.normalOpenLevelEdgeMap_action refinement element edge

/-- Refinement commutes with the ambient action on total branches. -/
theorem refinement_branch_commutes
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) (element : Ambient)
    (branch : (diagram.normalOpenLevelSemiGraph finer).TotalBranch) :
    (diagram.normalOpenLevelTransition refinement).totalBranchMap
        ((diagram.normalOpenLevel finer).cosetAction.branchAction element branch) =
      (diagram.normalOpenLevel coarser).cosetAction.branchAction element
        ((diagram.normalOpenLevelTransition refinement).totalBranchMap branch) :=
  diagram.normalOpenLevelTransition_totalBranchMap_action
    refinement element branch

/-- The incidence refinement map is equivariant for the ambient action. -/
theorem refinement_incidence_commutes
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) (element : Ambient)
    (point : IncidenceNode (LevelSemiGraph diagram finer)) :
    RefinementIncidenceMap diagram refinement
        (IncidenceNode.incidencePerm (LevelSemiGraph diagram finer)
          (diagram.normalOpenLevel finer).cosetAction element point) =
      IncidenceNode.incidencePerm (LevelSemiGraph diagram coarser)
        (diagram.normalOpenLevel coarser).cosetAction element
          (RefinementIncidenceMap diagram refinement point) := by
  cases point with
  | vertex point =>
      cases point with
      | inl vertex =>
          rw [IncidenceNode.incidencePerm_vertex]
          change IncidenceNode.vertex (Sum.inl _) = _
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_original,
            IncidenceNode.incidencePerm_vertex]
          apply congrArg (fun value => IncidenceNode.vertex (Sum.inl value))
          exact refinement_vertex_commutes diagram refinement element vertex
      | inr branch =>
          rw [IncidenceNode.incidencePerm_vertex]
          change RefinementIncidenceMap diagram refinement
              (IncidenceNode.vertex (Sum.inr
                (IncidenceNode.nonVerticialBranchPerm
                  (LevelSemiGraph diagram finer)
                  (diagram.normalOpenLevel finer).cosetAction element branch))) = _
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary,
            IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary,
            IncidenceNode.incidencePerm_vertex]
          change IncidenceNode.vertex (Sum.inr _) =
            IncidenceNode.vertex (Sum.inr _)
          apply congrArg (fun value => IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          exact refinement_branch_commutes diagram refinement element branch.1
  | edge edge =>
      rw [IncidenceNode.incidencePerm_edge,
        IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge,
        IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge,
        IncidenceNode.incidencePerm_edge]
      apply congrArg IncidenceNode.edge
      exact refinement_edge_commutes diagram refinement element edge
  | branch branch =>
      rw [IncidenceNode.incidencePerm_branch,
        IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch,
        IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch,
        IncidenceNode.incidencePerm_branch]
      apply congrArg IncidenceNode.branch
      exact refinement_branch_commutes diagram refinement element branch

/-- Every coarser incidence node has a finer lift. -/
theorem refinementIncidenceMap_surjective
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) :
    Function.Surjective (RefinementIncidenceMap diagram refinement) := by
  intro target
  cases target with
  | vertex target =>
      cases target with
      | inl vertex =>
          obtain ⟨source, equality⟩ :=
            diagram.normalOpenLevelVertexMap_surjective refinement vertex
          refine ⟨IncidenceNode.vertex (Sum.inl source), ?_⟩
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_original]
          apply congrArg (fun value => IncidenceNode.vertex (Sum.inl value))
          exact equality
      | inr branch =>
          obtain ⟨sourceBranch, branchEquality⟩ :=
            diagram.normalOpenLevelTransition_totalBranchMap_surjective
              refinement branch.1
          have sourceNone :
              (LevelSemiGraph diagram finer).coincidenceTotal sourceBranch = none := by
            cases sourceCoincidence :
                (LevelSemiGraph diagram finer).coincidenceTotal sourceBranch with
            | none => rfl
            | some vertex =>
                have targetCoincidence :=
                  (diagram.normalOpenLevelTransition refinement).map_coincidence
                    sourceBranch.1 sourceBranch.2 vertex sourceCoincidence
                have targetNone := branch.2
                change (LevelSemiGraph diagram coarser).coincidenceTotal
                  branch.1 = none at targetNone
                change (LevelSemiGraph diagram coarser).coincidenceTotal
                  ((diagram.normalOpenLevelTransition refinement).totalBranchMap
                    sourceBranch) = some _ at targetCoincidence
                rw [branchEquality, targetNone] at targetCoincidence
                cases targetCoincidence
          let source : (LevelSemiGraph diagram finer).NonVerticialBranch :=
            ⟨sourceBranch, sourceNone⟩
          refine ⟨IncidenceNode.vertex (Sum.inr source), ?_⟩
          rw [IncidenceNode.properIncidenceGraphHom_apply,
            IncidenceNode.properMap_vertex_boundary]
          apply congrArg (fun value => IncidenceNode.vertex (Sum.inr value))
          apply Subtype.ext
          exact branchEquality
  | edge edge =>
      obtain ⟨source, equality⟩ :=
        diagram.normalOpenLevelEdgeMap_surjective refinement edge
      refine ⟨IncidenceNode.edge source, ?_⟩
      rw [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_edge]
      apply congrArg IncidenceNode.edge
      exact equality
  | branch branch =>
      obtain ⟨source, equality⟩ :=
        diagram.normalOpenLevelTransition_totalBranchMap_surjective
          refinement branch
      refine ⟨IncidenceNode.branch source, ?_⟩
      rw [IncidenceNode.properIncidenceGraphHom_apply,
        IncidenceNode.properMap_branch, equality]

/-- Any ambient element acting trivially at a finer level also acts trivially
at every coarser level. -/
theorem incidenceActionHom_ker_le
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) :
    (IncidenceActionHom diagram finer).ker ≤
      (IncidenceActionHom diagram coarser).ker := by
  intro element finerKernel
  rw [MonoidHom.mem_ker] at finerKernel ⊢
  apply Subtype.ext
  apply Equiv.ext
  intro target
  obtain ⟨source, rfl⟩ :=
    refinementIncidenceMap_surjective diagram refinement target
  have finerPoint :
      IncidenceNode.incidencePerm (LevelSemiGraph diagram finer)
          (diagram.normalOpenLevel finer).cosetAction element source = source := by
    have equality := congrArg
      (fun automorphism : UniversalVertex.graphAutomorphismSubgroup
          (IncidenceGraph diagram finer) => automorphism.1 source)
      finerKernel
    change IncidenceNode.incidencePerm (LevelSemiGraph diagram finer)
      (diagram.normalOpenLevel finer).cosetAction element source = source at equality
    exact equality
  change IncidenceNode.incidencePerm (LevelSemiGraph diagram coarser)
      (diagram.normalOpenLevel coarser).cosetAction element
        (RefinementIncidenceMap diagram refinement source) =
    RefinementIncidenceMap diagram refinement source
  rw [← refinement_incidence_commutes diagram refinement element source,
    finerPoint]

/-- Quotient the finite-level ambient symmetry group along a normal-open
refinement. -/
noncomputable def symmetryTransition
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) :
    LevelSymmetries diagram finer →* LevelSymmetries diagram coarser :=
  MonoidHom.liftOfSurjective
      (IncidenceActionHom diagram finer).rangeRestrict
      (IncidenceActionHom diagram finer).rangeRestrict_surjective
    ⟨(IncidenceActionHom diagram coarser).rangeRestrict, by
      intro element sourceKernel
      rw [MonoidHom.mem_ker] at sourceKernel ⊢
      have sourceKernel' :
          (IncidenceActionHom diagram finer) element = 1 :=
        congrArg Subtype.val sourceKernel
      have targetKernel' :
          (IncidenceActionHom diagram coarser) element = 1 :=
        MonoidHom.mem_ker.mp <|
          incidenceActionHom_ker_le diagram refinement <|
            MonoidHom.mem_ker.mpr sourceKernel'
      apply Subtype.ext
      exact targetKernel'⟩

@[simp]
theorem symmetryTransition_rangeRestrict
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser) (element : Ambient) :
    symmetryTransition diagram refinement
        ((IncidenceActionHom diagram finer).rangeRestrict element) =
      (IncidenceActionHom diagram coarser).rangeRestrict element := by
  exact MonoidHom.liftOfRightInverse_comp_apply
    (IncidenceActionHom diagram finer).rangeRestrict
    (Function.surjInv
      (IncidenceActionHom diagram finer).rangeRestrict_surjective)
    (Function.rightInverse_surjInv
      (IncidenceActionHom diagram finer).rangeRestrict_surjective)
    ⟨(IncidenceActionHom diagram coarser).rangeRestrict, by
      intro value sourceKernel
      rw [MonoidHom.mem_ker] at sourceKernel ⊢
      have sourceKernel' :
          (IncidenceActionHom diagram finer) value = 1 :=
        congrArg Subtype.val sourceKernel
      have targetKernel' :
          (IncidenceActionHom diagram coarser) value = 1 :=
        MonoidHom.mem_ker.mp <|
          incidenceActionHom_ker_le diagram refinement <|
            MonoidHom.mem_ker.mpr sourceKernel'
      apply Subtype.ext
      exact targetKernel'⟩ element

/-- Refinement of a chosen root vertex. -/
abbrev RefinedRoot
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex) :
    (LevelSemiGraph diagram coarser).Vertex :=
  diagram.normalOpenLevelVertexMap refinement finerRoot

@[simp]
theorem refinementIncidenceMap_root
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex) :
    RefinementIncidenceMap diagram refinement
        (IncidenceRoot diagram finer finerRoot) =
      IncidenceRoot diagram coarser
        (RefinedRoot diagram refinement finerRoot) :=
  rfl

/-- Canonical map of reduced-walk universal trees under refinement.  Mapped
backtracking is cancelled one step at a time by `UniversalVertex.mapHom`. -/
noncomputable def RefinementTreeMap
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex) :
    IncidenceTreeVertex diagram finer finerRoot →
      IncidenceTreeVertex diagram coarser
        (RefinedRoot diagram refinement finerRoot) :=
  UniversalVertex.mapHom (IncidenceGraph diagram finer)
    (IncidenceRoot diagram finer finerRoot)
    (IncidenceGraph diagram coarser)
    (RefinementIncidenceMap diagram refinement)

@[simp]
theorem refinementTreeMap_endpoint
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex)
    (point : IncidenceTreeVertex diagram finer finerRoot) :
    (RefinementTreeMap diagram refinement finerRoot point).endpoint =
      RefinementIncidenceMap diagram refinement point.endpoint :=
  UniversalVertex.mapHom_endpoint _ _ _ _ _

@[simp]
theorem refinementTreeMap_base
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex) :
    RefinementTreeMap diagram refinement finerRoot
        (UniversalVertex.base (IncidenceGraph diagram finer)
          (IncidenceRoot diagram finer finerRoot)) =
      UniversalVertex.base (IncidenceGraph diagram coarser)
        (IncidenceRoot diagram coarser
          (RefinedRoot diagram refinement finerRoot)) :=
  rfl

theorem refinementTreeMap_adj
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex)
    {first second : IncidenceTreeVertex diagram finer finerRoot}
    (adjacent : (UniversalVertex.tree (IncidenceGraph diagram finer)
      (IncidenceRoot diagram finer finerRoot)).Adj first second) :
    (UniversalVertex.tree (IncidenceGraph diagram coarser)
      (IncidenceRoot diagram coarser
        (RefinedRoot diagram refinement finerRoot))).Adj
      (RefinementTreeMap diagram refinement finerRoot first)
      (RefinementTreeMap diagram refinement finerRoot second) :=
  UniversalVertex.mapHom_adj _ _ _ _ adjacent

/-- Refinement intertwines every finite-level symmetry with its quotient
symmetry. -/
theorem refinement_symmetry_commutes
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (symmetry : LevelSymmetries diagram finer)
    (point : IncidenceNode (LevelSemiGraph diagram finer)) :
    RefinementIncidenceMap diagram refinement (symmetry.1.1 point) =
      (symmetryTransition diagram refinement symmetry).1.1
        (RefinementIncidenceMap diagram refinement point) := by
  obtain ⟨element, symmetryEquality⟩ := symmetry.2
  have sourcePermutation : symmetry.1.1 =
      IncidenceNode.incidencePerm (LevelSemiGraph diagram finer)
        (diagram.normalOpenLevel finer).cosetAction element :=
    congrArg Subtype.val symmetryEquality.symm
  rw [sourcePermutation]
  have symmetryAsRange : symmetry =
      (IncidenceActionHom diagram finer).rangeRestrict element := by
    apply Subtype.ext
    exact symmetryEquality.symm
  rw [symmetryAsRange, symmetryTransition_rangeRestrict]
  exact refinement_incidence_commutes diagram refinement element point

/-- The quotient symmetry associated to a lifted deck transformation under
refinement. -/
noncomputable def transitionedSymmetry
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex)
    (transformation : DeckGroup diagram finer finerRoot) :
    LevelSymmetries diagram coarser :=
  symmetryTransition diagram refinement
    (UniversalVertex.LiftedDeckTransformation.baseSymmetry transformation)

/-- Image of the transformed source base point in the coarser universal
tree. -/
noncomputable def transitionedBaseImage
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex)
    (transformation : DeckGroup diagram finer finerRoot) :
    IncidenceTreeVertex diagram coarser
      (RefinedRoot diagram refinement finerRoot) :=
  RefinementTreeMap diagram refinement finerRoot <|
    transformation.1 <|
      UniversalVertex.base (IncidenceGraph diagram finer)
        (IncidenceRoot diagram finer finerRoot)

/-- The quotient symmetry carries the coarser root to the endpoint selected
by the transformed source base point. -/
theorem transitionedBaseImage_endpoint
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex)
    (transformation : DeckGroup diagram finer finerRoot) :
    (transitionedSymmetry diagram refinement finerRoot transformation).1.1
        (IncidenceRoot diagram coarser
          (RefinedRoot diagram refinement finerRoot)) =
      (transitionedBaseImage diagram refinement finerRoot
        transformation).endpoint := by
  rw [transitionedBaseImage, refinementTreeMap_endpoint,
    UniversalVertex.LiftedDeckTransformation.endpoint_apply]
  exact (refinement_symmetry_commutes diagram refinement
    (UniversalVertex.LiftedDeckTransformation.baseSymmetry transformation)
    (IncidenceRoot diagram finer finerRoot)).symm

/-- Transition a composite deck transformation by its quotient symmetry and
the image of one base point. -/
noncomputable def deckTransitionToFun
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex)
    (transformation : DeckGroup diagram finer finerRoot) :
    DeckGroup diagram coarser (RefinedRoot diagram refinement finerRoot) :=
  UniversalVertex.LiftedDeckTransformation.between
    (transitionedSymmetry diagram refinement finerRoot transformation)
    (UniversalVertex.base (IncidenceGraph diagram coarser)
      (IncidenceRoot diagram coarser
        (RefinedRoot diagram refinement finerRoot)))
    (transitionedBaseImage diagram refinement finerRoot transformation)
    (transitionedBaseImage_endpoint diagram refinement finerRoot transformation)

@[simp]
theorem deckTransitionToFun_base
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex)
    (transformation : DeckGroup diagram finer finerRoot) :
    (deckTransitionToFun diagram refinement finerRoot transformation).1
        (UniversalVertex.base (IncidenceGraph diagram coarser)
          (IncidenceRoot diagram coarser
            (RefinedRoot diagram refinement finerRoot))) =
      transitionedBaseImage diagram refinement finerRoot transformation :=
  UniversalVertex.LiftedDeckTransformation.between_apply_first _ _ _ _

/-- The transitioned deck transformation is the unique one commuting with
the canonical map of universal trees. -/
theorem deckTransitionToFun_commutes
    {finer coarser : OpenNormalSubgroup Ambient}
    (refinement : finer ⟶ coarser)
    (finerRoot : (LevelSemiGraph diagram finer).Vertex)
    (transformation : DeckGroup diagram finer finerRoot)
    (point : IncidenceTreeVertex diagram finer finerRoot) :
    RefinementTreeMap diagram refinement finerRoot
        (transformation.1 point) =
      (deckTransitionToFun diagram refinement finerRoot transformation).1
        (RefinementTreeMap diagram refinement finerRoot point) := by
  let sourceGraph := IncidenceGraph diagram finer
  let sourceRoot := IncidenceRoot diagram finer finerRoot
  let targetGraph := IncidenceGraph diagram coarser
  let targetRoot := IncidenceRoot diagram coarser
    (RefinedRoot diagram refinement finerRoot)
  let first : UniversalVertex sourceGraph sourceRoot →
      UniversalVertex targetGraph targetRoot :=
    fun value => RefinementTreeMap diagram refinement finerRoot
      (transformation.1 value)
  let second : UniversalVertex sourceGraph sourceRoot →
      UniversalVertex targetGraph targetRoot :=
    fun value =>
      (deckTransitionToFun diagram refinement finerRoot transformation).1
        (RefinementTreeMap diagram refinement finerRoot value)
  have endpointEquality : ∀ value, (first value).endpoint =
      (second value).endpoint := by
    intro value
    change (RefinementTreeMap diagram refinement finerRoot
        (transformation.1 value)).endpoint =
      ((deckTransitionToFun diagram refinement finerRoot transformation).1
        (RefinementTreeMap diagram refinement finerRoot value)).endpoint
    rw [refinementTreeMap_endpoint,
      UniversalVertex.LiftedDeckTransformation.endpoint_apply]
    change RefinementIncidenceMap diagram refinement
        ((UniversalVertex.LiftedDeckTransformation.baseSymmetry
          transformation).1.1 value.endpoint) = _
    unfold deckTransitionToFun
    rw [UniversalVertex.LiftedDeckTransformation.between_endpoint_apply,
      refinementTreeMap_endpoint]
    exact refinement_symmetry_commutes diagram refinement
      (UniversalVertex.LiftedDeckTransformation.baseSymmetry transformation)
      value.endpoint
  have firstAdjacent : ∀ {value neighbor},
      (UniversalVertex.tree sourceGraph sourceRoot).Adj value neighbor →
        (UniversalVertex.tree targetGraph targetRoot).Adj
          (first value) (first neighbor) := by
    intro value neighbor adjacent
    exact refinementTreeMap_adj diagram refinement finerRoot <|
      (UniversalVertex.LiftedDeckTransformation.adjacency_apply_iff
        transformation value neighbor).mpr adjacent
  have secondAdjacent : ∀ {value neighbor},
      (UniversalVertex.tree sourceGraph sourceRoot).Adj value neighbor →
        (UniversalVertex.tree targetGraph targetRoot).Adj
          (second value) (second neighbor) := by
    intro value neighbor adjacent
    exact (UniversalVertex.LiftedDeckTransformation.adjacency_apply_iff
      (deckTransitionToFun diagram refinement finerRoot transformation)
      _ _).mpr (refinementTreeMap_adj diagram refinement finerRoot adjacent)
  have atBase : first (UniversalVertex.base sourceGraph sourceRoot) =
      second (UniversalVertex.base sourceGraph sourceRoot) := by
    change RefinementTreeMap diagram refinement finerRoot
        (transformation.1 (UniversalVertex.base sourceGraph sourceRoot)) =
      (deckTransitionToFun diagram refinement finerRoot transformation).1
        (RefinementTreeMap diagram refinement finerRoot
          (UniversalVertex.base sourceGraph sourceRoot))
    rw [refinementTreeMap_base, deckTransitionToFun_base]
    rfl
  have mapEquality := UniversalVertex.map_eq_of_endpoint_eq_adj
    sourceGraph sourceRoot targetGraph targetRoot first second
      endpointEquality firstAdjacent secondAdjacent
      (UniversalVertex.base sourceGraph sourceRoot) atBase
  exact congrFun mapEquality point

end SourceRawNormalOpenCombinatorialUniversalCover

end SourceCombinatorialUniversalCover

end Iut
