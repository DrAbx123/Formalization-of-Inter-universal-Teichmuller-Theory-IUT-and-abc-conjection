/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
# Source semi-graphs

This module formalizes the branch-set definition at the beginning of
*Semi-graphs of Anabelioids*, Section 1.  An edge has a two-element type of
branches, and its coincidence map is partial: `some vertex` means that the
branch abuts that vertex, while `none` is the paper's extra symbol outside the
vertex set.

Keeping branches as a dependent family makes the source requirement that the
two-element branch sets of distinct edges be disjoint literal in the type
theory.  In particular, unlike a simple graph, this representation retains
loops, parallel edges, open edges, and isolated edges.
-/

namespace Iut

universe u

/-- The branch-set definition of a semi-graph from *Semi-graphs of
Anabelioids*, Section 1, pp. 11--12.  `Option Vertex` represents the disjoint
union of the vertex set with the single nonverticial symbol used in the paper.
-/
structure SourceSemiGraph where
  Vertex : Type u
  Edge : Type u
  Branch : Edge → Type u
  branchFintype : ∀ edge, Fintype (Branch edge)
  branch_card : ∀ edge, @Fintype.card (Branch edge) (branchFintype edge) = 2
  coincidence : ∀ edge, Branch edge → Option Vertex

namespace SourceSemiGraph

variable (G : SourceSemiGraph.{u})

instance instFintypeBranch (edge : G.Edge) : Fintype (G.Branch edge) :=
  G.branchFintype edge

/-- A branch together with the edge to which it belongs. -/
def TotalBranch := Σ edge, G.Branch edge

/-- The edge supporting a total branch. -/
def TotalBranch.edge (branch : G.TotalBranch) : G.Edge := branch.1

/-- The coincidence map on total branches. -/
def coincidenceTotal (branch : G.TotalBranch) : Option G.Vertex :=
  G.coincidence branch.1 branch.2

/-- The verticial portion of an edge: the branches that abut a vertex. -/
def verticialPortion (edge : G.Edge) : Set (G.Branch edge) :=
  {branch | ∃ vertex, G.coincidence edge branch = some vertex}

/-- The source's verticial cardinality of an edge. -/
noncomputable def verticialCardinality (edge : G.Edge) : Nat :=
  (G.verticialPortion edge).ncard

/-- A branch abuts a vertex when its coincidence value is that vertex. -/
def BranchAbuts {edge : G.Edge} (branch : G.Branch edge)
    (vertex : G.Vertex) : Prop :=
  G.coincidence edge branch = some vertex

/-- An edge abuts a vertex when one of its branches does. -/
def EdgeAbuts (edge : G.Edge) (vertex : G.Vertex) : Prop :=
  ∃ branch : G.Branch edge, G.BranchAbuts branch vertex

/-- The type of all branches abutting a fixed vertex. -/
def IncidentBranch (vertex : G.Vertex) :=
  {branch : G.TotalBranch // G.coincidenceTotal branch = some vertex}

/-- A component is either a vertex or an edge. -/
def Component := G.Vertex ⊕ G.Edge

/-- A closed edge has both of its branches in the verticial portion. -/
def IsClosed (edge : G.Edge) : Prop :=
  ∀ branch : G.Branch edge, ∃ vertex, G.BranchAbuts branch vertex

/-- An open edge has verticial cardinality strictly less than two. -/
def IsOpen (edge : G.Edge) : Prop :=
  G.verticialCardinality edge < 2

/-- An isolated edge has no verticial branches. -/
def IsIsolated (edge : G.Edge) : Prop :=
  ∀ branch, G.coincidence edge branch = none

/-- A graph is a semi-graph all of whose edges are closed. -/
def IsGraph : Prop :=
  ∀ edge, G.IsClosed edge

/-- Finiteness means finiteness of both the vertex and edge sets. -/
def IsFinite : Prop :=
  Finite G.Vertex ∧ Finite G.Edge

/-- Countability means countability of both the vertex and edge sets. -/
def IsCountable : Prop :=
  Countable G.Vertex ∧ Countable G.Edge

/-- A closed edge joins two vertices when its two distinct branches abut the
displayed vertices.  The vertices are intentionally allowed to coincide, so
loop edges are retained. -/
def Joins (edge : G.Edge) (first second : G.Vertex) : Prop :=
  ∃ firstBranch secondBranch : G.Branch edge,
    firstBranch ≠ secondBranch ∧
      G.BranchAbuts firstBranch first ∧
      G.BranchAbuts secondBranch second

/-- Two vertices are adjacent when a closed edge joins them.  Open edges do
not create adjacency between vertices. -/
def Adjacent (first second : G.Vertex) : Prop :=
  ∃ edge, G.Joins edge first second

/-- Source-faithful connectedness for a semi-graph.  In the verticial case,
every edge belongs to the component containing the vertices and all vertices
are joined by closed-edge paths.  The only connected case without vertices is
the paper's single isolated edge. -/
def IsConnected : Prop :=
  (Nonempty G.Vertex ∧
      (∀ edge, ∃ vertex, G.EdgeAbuts edge vertex) ∧
      ∀ first second,
        Relation.ReflTransGen G.Adjacent first second) ∨
    (IsEmpty G.Vertex ∧ Nonempty G.Edge ∧ Subsingleton G.Edge)

/-- Closed edges are coverticial when they abut exactly the same vertices. -/
def Coverticial (first second : G.Edge) : Prop :=
  G.IsClosed first ∧ G.IsClosed second ∧
    ∀ vertex, G.EdgeAbuts first vertex ↔ G.EdgeAbuts second vertex

/-- Local finiteness is finiteness of the set of edges abutting each vertex. -/
def IsLocallyFinite : Prop :=
  ∀ vertex, Set.Finite {edge | G.EdgeAbuts edge vertex}

/-- Untangled means that every closed edge joins two distinct vertices. -/
def IsUntangled : Prop :=
  ∀ edge, G.IsClosed edge →
    ∃ first second, first ≠ second ∧ G.Joins edge first second

theorem branch_card_eq_two (edge : G.Edge) : Fintype.card (G.Branch edge) = 2 :=
  G.branch_card edge

/-- Adjacency of vertices is symmetric. -/
theorem adjacent_comm {first second : G.Vertex} :
    G.Adjacent first second ↔ G.Adjacent second first := by
  constructor
  · rintro ⟨edge, firstBranch, secondBranch, distinct,
      firstAbuts, secondAbuts⟩
    exact ⟨edge, secondBranch, firstBranch, distinct.symm,
      secondAbuts, firstAbuts⟩
  · rintro ⟨edge, secondBranch, firstBranch, distinct,
      secondAbuts, firstAbuts⟩
    exact ⟨edge, firstBranch, secondBranch, distinct.symm,
      firstAbuts, secondAbuts⟩

/-- A connected semi-graph with vertices has no isolated edge. -/
theorem IsConnected.edge_abuts_of_nonempty
    (connected : G.IsConnected) [Nonempty G.Vertex] (edge : G.Edge) :
    ∃ vertex, G.EdgeAbuts edge vertex := by
  rcases connected with verticial | isolated
  · exact verticial.2.1 edge
  · exact False.elim <| not_isEmpty_of_nonempty G.Vertex isolated.1

/-- A connected semi-graph without vertices has an edge. -/
theorem IsConnected.nonemptyEdge_of_isEmpty
    (connected : G.IsConnected) [IsEmpty G.Vertex] : Nonempty G.Edge := by
  rcases connected with verticial | isolated
  · exact False.elim <| isEmptyElim (Classical.choice verticial.1)
  · exact isolated.2.1

/-- A connected semi-graph without vertices has at most one edge. -/
theorem IsConnected.subsingletonEdge_of_isEmpty
    (connected : G.IsConnected) [IsEmpty G.Vertex] : Subsingleton G.Edge := by
  rcases connected with verticial | isolated
  · exact False.elim <| isEmptyElim (Classical.choice verticial.1)
  · exact isolated.2.2

/-- The unique edge of a connected vertex-free semi-graph. -/
noncomputable def IsConnected.uniqueEdge
    (connected : G.IsConnected) [IsEmpty G.Vertex] : G.Edge :=
  Classical.choice connected.nonemptyEdge_of_isEmpty

/-- The unique edge in the vertex-free connected case is isolated. -/
theorem IsConnected.edge_isIsolated_of_isEmpty
    (_connected : G.IsConnected) [IsEmpty G.Vertex] (edge : G.Edge) :
    G.IsIsolated edge := by
  intro branch
  cases coincidence : G.coincidence edge branch with
  | none => rfl
  | some vertex => exact isEmptyElim vertex

/-- The verticial cardinality never exceeds the two-element branch fiber. -/
theorem verticialCardinality_le_two (edge : G.Edge) :
    G.verticialCardinality edge ≤ 2 := by
  rw [verticialCardinality, ← G.branch_card edge]
  simpa [Nat.card_eq_fintype_card] using
    Set.ncard_le_card (G.verticialPortion edge)

/-- The branchwise and cardinality formulations of a closed edge agree. -/
theorem isClosed_iff_verticialCardinality_eq_two (edge : G.Edge) :
    G.IsClosed edge ↔ G.verticialCardinality edge = 2 := by
  rw [verticialCardinality, ← G.branch_card edge]
  constructor
  · intro closed
    have portion_univ : G.verticialPortion edge = Set.univ := by
      ext branch
      simp only [verticialPortion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact closed branch
    rw [portion_univ, Set.ncard_univ, Nat.card_eq_fintype_card]
  · intro cardinality branch
    have portion_univ : G.verticialPortion edge = Set.univ := by
      rw [Set.eq_univ_iff_ncard, Nat.card_eq_fintype_card]
      exact cardinality
    have : branch ∈ G.verticialPortion edge := by
      rw [portion_univ]
      exact Set.mem_univ branch
    exact this

/-- Thus the source's two descriptions of an open edge agree as well. -/
theorem isOpen_iff_not_isClosed (edge : G.Edge) :
    G.IsOpen edge ↔ ¬G.IsClosed edge := by
  rw [G.isClosed_iff_verticialCardinality_eq_two]
  unfold IsOpen
  have bound := G.verticialCardinality_le_two edge
  omega

/-- An isolated edge has verticial cardinality zero. -/
theorem isIsolated_iff_verticialCardinality_eq_zero (edge : G.Edge) :
    G.IsIsolated edge ↔ G.verticialCardinality edge = 0 := by
  rw [verticialCardinality, Set.ncard_eq_zero]
  constructor
  · intro isolated
    ext branch
    constructor
    · intro branch_mem
      obtain ⟨vertex, abuts⟩ := branch_mem
      rw [isolated branch] at abuts
      simp at abuts
    · simp
  · intro portion_empty branch
    cases coincidence_eq : G.coincidence edge branch with
    | none => rfl
    | some vertex =>
        exfalso
        have : branch ∈ G.verticialPortion edge := ⟨vertex, coincidence_eq⟩
        rw [portion_empty] at this
        exact this

/-- A morphism of semi-graphs has vertex and edge maps and a bijection on each
two-branch fiber.  Compatibility is required only on the source verticial
portion, exactly as in the paper; a nonverticial source branch may become
verticial in the target. -/
structure Hom (G H : SourceSemiGraph.{u}) where
  vertexMap : G.Vertex → H.Vertex
  edgeMap : G.Edge → H.Edge
  branchEquiv : ∀ edge, G.Branch edge ≃ H.Branch (edgeMap edge)
  map_coincidence :
    ∀ edge branch vertex,
      G.coincidence edge branch = some vertex →
        H.coincidence (edgeMap edge) (branchEquiv edge branch) =
          some (vertexMap vertex)

namespace Hom

variable {G H K : SourceSemiGraph.{u}}

/-- Two semi-graph morphisms are equal when their vertex, edge, and dependent
branch maps agree pointwise. -/
@[ext]
theorem ext {first second : G.Hom H}
    (vertexMap : ∀ vertex, first.vertexMap vertex = second.vertexMap vertex)
    (edgeMap : ∀ edge, first.edgeMap edge = second.edgeMap edge)
    (branchEquiv : ∀ edge branch,
      HEq (first.branchEquiv edge branch) (second.branchEquiv edge branch)) :
    first = second := by
  cases first with
  | mk firstVertexMap firstEdgeMap firstBranchEquiv firstCoincidence =>
    cases second with
    | mk secondVertexMap secondEdgeMap secondBranchEquiv secondCoincidence =>
      dsimp at vertexMap edgeMap branchEquiv
      have vertexMapEquality : firstVertexMap = secondVertexMap :=
        funext vertexMap
      have edgeMapEquality : firstEdgeMap = secondEdgeMap :=
        funext edgeMap
      cases vertexMapEquality
      cases edgeMapEquality
      have branchEquivEquality :
          firstBranchEquiv = secondBranchEquiv := by
        funext edge
        apply Equiv.ext
        intro branch
        exact eq_of_heq (branchEquiv edge branch)
      cases branchEquivEquality
      rfl

/-- The identity morphism of a semi-graph. -/
def id (G : SourceSemiGraph.{u}) : G.Hom G where
  vertexMap := fun vertex => vertex
  edgeMap := fun edge => edge
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro _ _ _ coincidence
    exact coincidence

/-- Composition of source semi-graph morphisms. -/
def comp (first : G.Hom H) (second : H.Hom K) : G.Hom K where
  vertexMap := second.vertexMap ∘ first.vertexMap
  edgeMap := second.edgeMap ∘ first.edgeMap
  branchEquiv := fun edge =>
    (first.branchEquiv edge).trans (second.branchEquiv (first.edgeMap edge))
  map_coincidence := by
    intro edge branch vertex coincidence
    exact second.map_coincidence _ _ _
      (first.map_coincidence edge branch vertex coincidence)

@[simp]
theorem comp_vertexMap (first : G.Hom H) (second : H.Hom K)
    (vertex : G.Vertex) :
    (first.comp second).vertexMap vertex =
      second.vertexMap (first.vertexMap vertex) :=
  rfl

@[simp]
theorem comp_edgeMap (first : G.Hom H) (second : H.Hom K)
    (edge : G.Edge) :
    (first.comp second).edgeMap edge = second.edgeMap (first.edgeMap edge) :=
  rfl

@[simp]
theorem comp_branchEquiv_apply (first : G.Hom H) (second : H.Hom K)
    (edge : G.Edge) (branch : G.Branch edge) :
    (first.comp second).branchEquiv edge branch =
      second.branchEquiv (first.edgeMap edge)
        (first.branchEquiv edge branch) :=
  rfl

/-- Composition of source semi-graph morphisms is associative. -/
theorem comp_assoc {L : SourceSemiGraph.{u}}
    (first : G.Hom H) (second : H.Hom K) (third : K.Hom L) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply ext
  · intro vertex
    rfl
  · intro edge
    rfl
  · intro edge branch
    rfl

/-- The induced map on total branches. -/
def totalBranchMap (map : G.Hom H) : G.TotalBranch → H.TotalBranch
  | ⟨edge, branch⟩ => ⟨map.edgeMap edge, map.branchEquiv edge branch⟩

/-- A semi-graph morphism maps an incident branch to the corresponding
incident branch at the image vertex. -/
def incidentBranchMap (map : G.Hom H) (vertex : G.Vertex) :
    G.IncidentBranch vertex → H.IncidentBranch (map.vertexMap vertex)
  | ⟨⟨edge, branch⟩, coincidence⟩ =>
      ⟨⟨map.edgeMap edge, map.branchEquiv edge branch⟩,
        map.map_coincidence edge branch vertex coincidence⟩

/-- An immersion is locally injective on the branches abutting each vertex. -/
def IsImmersion (map : G.Hom H) : Prop :=
  ∀ vertex, Function.Injective (map.incidentBranchMap vertex)

/-- An excision is locally bijective on the branches abutting each vertex. -/
def IsExcision (map : G.Hom H) : Prop :=
  ∀ vertex, Function.Bijective (map.incidentBranchMap vertex)

/-- Properness means that no nonverticial branch becomes verticial.  Since the
branch map is bijective and verticial branches are already preserved, this is
equivalent to preservation of the source's verticial cardinalities. -/
def IsProper (map : G.Hom H) : Prop :=
  ∀ edge branch,
    (∃ vertex, G.coincidence edge branch = some vertex) ↔
      ∃ vertex,
        H.coincidence (map.edgeMap edge) (map.branchEquiv edge branch) =
          some vertex

/-- Proper semi-graph morphisms are closed under composition. -/
theorem IsProper.comp {first : G.Hom H} {second : H.Hom K}
    (firstProper : first.IsProper) (secondProper : second.IsProper) :
    (first.comp second).IsProper := by
  intro edge branch
  exact (firstProper edge branch).trans
    (secondProper (first.edgeMap edge) (first.branchEquiv edge branch))

/-- A graph-covering is a proper excision. -/
def IsGraphCovering (map : G.Hom H) : Prop :=
  map.IsProper ∧ map.IsExcision

/-- The vertex fiber of a semi-graph morphism. -/
def VertexFiber (map : G.Hom H) (vertex : H.Vertex) :=
  {sourceVertex // map.vertexMap sourceVertex = vertex}

/-- The edge fiber of a semi-graph morphism. -/
def EdgeFiber (map : G.Hom H) (edge : H.Edge) :=
  {sourceEdge // map.edgeMap sourceEdge = edge}

/-- A finite graph-covering is a graph-covering with finite component fibers.
Branch fibers are then finite because every edge has exactly two branches. -/
def IsFiniteGraphCovering (map : G.Hom H) : Prop :=
  map.IsGraphCovering ∧
    (∀ vertex, Finite (map.VertexFiber vertex)) ∧
    ∀ edge, Finite (map.EdgeFiber edge)

/-- The target verticial portion pulled back along the branch equivalence. -/
def targetVerticialPreimage (map : G.Hom H) (edge : G.Edge) :
    Set (G.Branch edge) :=
  {branch |
    map.branchEquiv edge branch ∈
      H.verticialPortion (map.edgeMap edge)}

theorem map_branch_abuts (map : G.Hom H) {edge : G.Edge}
    {branch : G.Branch edge} {vertex : G.Vertex}
    (abuts : G.BranchAbuts branch vertex) :
    H.BranchAbuts (map.branchEquiv edge branch) (map.vertexMap vertex) :=
  map.map_coincidence edge branch vertex abuts

theorem map_edge_abuts (map : G.Hom H) {edge : G.Edge}
    {vertex : G.Vertex} (abuts : G.EdgeAbuts edge vertex) :
    H.EdgeAbuts (map.edgeMap edge) (map.vertexMap vertex) := by
  obtain ⟨branch, branch_abuts⟩ := abuts
  exact ⟨map.branchEquiv edge branch,
    map.map_branch_abuts branch_abuts⟩

/-- The source verticial portion injects into the pulled-back target
verticial portion for every semi-graph morphism. -/
theorem verticialPortion_subset_targetPreimage (map : G.Hom H)
    (edge : G.Edge) :
    G.verticialPortion edge ⊆ map.targetVerticialPreimage edge := by
  intro branch branch_mem
  obtain ⟨vertex, coincidence⟩ := branch_mem
  exact ⟨map.vertexMap vertex,
    map.map_coincidence edge branch vertex coincidence⟩

/-- Pullback along the branch equivalence preserves the cardinality of the
target verticial portion. -/
theorem targetVerticialPreimage_ncard (map : G.Hom H) (edge : G.Edge) :
    (map.targetVerticialPreimage edge).ncard =
      (H.verticialPortion (map.edgeMap edge)).ncard := by
  apply Set.ncard_congr
      (fun branch _ => map.branchEquiv edge branch)
  · intro branch branch_mem
    exact branch_mem
  · intro first second _ _ equality
    exact (map.branchEquiv edge).injective equality
  · intro targetBranch target_mem
    let sourceBranch := (map.branchEquiv edge).symm targetBranch
    refine ⟨sourceBranch, ?_, ?_⟩
    · change map.branchEquiv edge sourceBranch ∈
        H.verticialPortion (map.edgeMap edge)
      simpa [sourceBranch] using target_mem
    · exact (map.branchEquiv edge).apply_symm_apply targetBranch

/-- The branchwise formulation of properness is equivalent to the paper's
literal requirement that verticial cardinalities be preserved. -/
theorem isProper_iff_preserves_verticialCardinality (map : G.Hom H) :
    map.IsProper ↔
      ∀ edge,
        G.verticialCardinality edge =
          H.verticialCardinality (map.edgeMap edge) := by
  constructor
  · intro proper edge
    unfold SourceSemiGraph.verticialCardinality
    calc
      (G.verticialPortion edge).ncard =
          (map.targetVerticialPreimage edge).ncard := by
        congr 1
        ext branch
        exact proper edge branch
      _ = (H.verticialPortion (map.edgeMap edge)).ncard :=
        map.targetVerticialPreimage_ncard edge
  · intro preserves edge branch
    constructor
    · intro source_mem
      exact map.verticialPortion_subset_targetPreimage edge source_mem
    · intro target_mem
      have portion_eq :
          G.verticialPortion edge =
            map.targetVerticialPreimage edge := by
        apply Set.eq_of_subset_of_ncard_le
          (map.verticialPortion_subset_targetPreimage edge)
        have cardinality_eq :
            (map.targetVerticialPreimage edge).ncard =
              (G.verticialPortion edge).ncard := by
          rw [map.targetVerticialPreimage_ncard]
          simpa [SourceSemiGraph.verticialCardinality] using
            (preserves edge).symm
        exact cardinality_eq.le
      have : branch ∈ map.targetVerticialPreimage edge := target_mem
      rw [← portion_eq] at this
      exact this

theorem isExcision_isImmersion {map : G.Hom H}
    (excision : map.IsExcision) : map.IsImmersion :=
  fun vertex => (excision vertex).1

end Hom

/-- The data selecting a sub-semi-graph.  Its coincidence map is forced by the
paper's clauses (b)--(c): branches retain precisely those abutments whose
vertices were selected. -/
structure Sub (G : SourceSemiGraph.{u}) where
  vertexSet : Set G.Vertex
  edgeSet : Set G.Edge

namespace Sub

variable {G : SourceSemiGraph.{u}} (S : G.Sub)

/-- Restrict a vertex to the selected vertex set, returning the nonverticial
symbol when it was omitted. -/
noncomputable def restrictVertex (vertex : G.Vertex) : Option S.vertexSet :=
  by
    classical
    exact if member : vertex ∈ S.vertexSet then some ⟨vertex, member⟩ else none

/-- The semi-graph determined by a set of vertices and a set of edges. -/
noncomputable def toSemiGraph : SourceSemiGraph.{u} where
  Vertex := S.vertexSet
  Edge := S.edgeSet
  Branch := fun edge => G.Branch edge.1
  branchFintype := fun edge => G.branchFintype edge.1
  branch_card := fun edge => G.branch_card edge.1
  coincidence := fun edge branch =>
    (G.coincidence edge.1 branch).bind S.restrictVertex

/-- A selected branch abuts exactly when its ambient abutment vertex was also
selected. -/
theorem coincidence_eq_some_iff {edge : S.edgeSet}
    {branch : G.Branch edge.1} {vertex : S.vertexSet} :
    S.toSemiGraph.coincidence edge branch = some vertex ↔
      G.coincidence edge.1 branch = some vertex.1 := by
  classical
  change (G.coincidence edge.1 branch).bind S.restrictVertex = some vertex ↔ _
  cases coincidence : G.coincidence edge.1 branch with
  | none => simp
  | some ambientVertex =>
      by_cases member : ambientVertex ∈ S.vertexSet
      · simp only [Option.bind_some]
        unfold restrictVertex
        rw [dif_pos member]
        simp only [Option.some.injEq, Subtype.ext_iff]
      · simp only [Option.bind_some]
        unfold restrictVertex
        rw [dif_neg member]
        simp only [reduceCtorEq, false_iff, Option.some.injEq]
        intro equality
        apply member
        rw [equality]
        exact vertex.2

/-- The canonical inclusion morphism of the selected sub-semi-graph into its
ambient semi-graph. -/
noncomputable def inclusion : S.toSemiGraph.Hom G where
  vertexMap := Subtype.val
  edgeMap := Subtype.val
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro edge branch vertex coincidence
    exact S.coincidence_eq_some_iff.mp coincidence

end Sub

/-- A branch that does not abut any vertex. -/
def NonVerticialBranch :=
  {branch : G.TotalBranch // G.coincidenceTotal branch = none}

/-- The vertex type of the compactification: old vertices together with one
new vertex for every nonverticial branch. -/
def CompactVertex := G.Vertex ⊕ G.NonVerticialBranch

/-- The coincidence map used by the compactification. -/
def compactCoincidence (edge : G.Edge) (branch : G.Branch edge) :
    Option G.CompactVertex :=
  match coincidence : G.coincidence edge branch with
  | some vertex => some (Sum.inl vertex)
  | none => some (Sum.inr ⟨⟨edge, branch⟩, coincidence⟩)

/-- The compactification from Section 1: append a new vertex to every
nonverticial branch. -/
def compactification : SourceSemiGraph.{u} where
  Vertex := G.CompactVertex
  Edge := G.Edge
  Branch := G.Branch
  branchFintype := G.branchFintype
  branch_card := G.branch_card
  coincidence := G.compactCoincidence

@[simp]
theorem compactification_coincidence_of_some {edge : G.Edge}
    {branch : G.Branch edge} {vertex : G.Vertex}
    (coincidence : G.coincidence edge branch = some vertex) :
    G.compactification.coincidence edge branch =
      some (Sum.inl vertex) := by
  change G.compactCoincidence edge branch = some (Sum.inl vertex)
  unfold compactCoincidence
  split
  next value valueCoincidence =>
    have value_eq : value = vertex :=
      Option.some.inj (valueCoincidence.symm.trans coincidence)
    subst value
    rfl
  next noneCoincidence =>
    have impossible : (none : Option G.Vertex) = some vertex :=
      noneCoincidence.symm.trans coincidence
    cases impossible

@[simp]
theorem compactification_coincidence_of_none {edge : G.Edge}
    {branch : G.Branch edge}
    (coincidence : G.coincidence edge branch = none) :
    G.compactification.coincidence edge branch =
      some (Sum.inr ⟨⟨edge, branch⟩, coincidence⟩) := by
  change G.compactCoincidence edge branch =
    some (Sum.inr ⟨⟨edge, branch⟩, coincidence⟩)
  unfold compactCoincidence
  split
  next vertex vertexCoincidence =>
    have impossible : some vertex = (none : Option G.Vertex) :=
      vertexCoincidence.symm.trans coincidence
    cases impossible
  next _ => rfl

/-- Every edge of the compactification is closed. -/
theorem compactification_isGraph : G.compactification.IsGraph := by
  intro edge branch
  unfold BranchAbuts
  cases coincidence : G.coincidence edge branch with
  | some vertex =>
      exact ⟨Sum.inl vertex,
        G.compactification_coincidence_of_some coincidence⟩
  | none =>
      exact ⟨Sum.inr ⟨⟨edge, branch⟩, coincidence⟩,
        G.compactification_coincidence_of_none coincidence⟩

/-- The canonical morphism from a semi-graph to its compactification. -/
def compactificationInclusion : G.Hom G.compactification where
  vertexMap := Sum.inl
  edgeMap := id
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro edge branch vertex coincidence
    simpa using G.compactification_coincidence_of_some coincidence

namespace Hom

variable {G H : SourceSemiGraph.{u}}

/-- The vertex map induced on compactifications.  A newly appended source
vertex maps either to an old target vertex, when the morphism closes that
branch, or to the target vertex appended at the image branch. -/
def compactVertexMap (map : G.Hom H) : G.CompactVertex → H.CompactVertex
  | Sum.inl vertex => Sum.inl (map.vertexMap vertex)
  | Sum.inr branch =>
      match coincidence :
          H.coincidence (map.edgeMap branch.1.1)
            (map.branchEquiv branch.1.1 branch.1.2) with
      | some vertex => Sum.inl vertex
      | none => Sum.inr
          ⟨map.totalBranchMap branch.1, coincidence⟩

@[simp]
theorem compactVertexMap_boundary_of_some (map : G.Hom H)
    (branch : G.NonVerticialBranch) {vertex : H.Vertex}
    (coincidence :
      H.coincidence (map.edgeMap branch.1.1)
        (map.branchEquiv branch.1.1 branch.1.2) = some vertex) :
    map.compactVertexMap (Sum.inr branch) = Sum.inl vertex := by
  rw [compactVertexMap]
  split
  next value valueCoincidence =>
    have value_eq : value = vertex :=
      Option.some.inj (valueCoincidence.symm.trans coincidence)
    subst value
    rfl
  next noneCoincidence =>
    have impossible : (none : Option H.Vertex) = some vertex :=
      noneCoincidence.symm.trans coincidence
    cases impossible

@[simp]
theorem compactVertexMap_boundary_of_none (map : G.Hom H)
    (branch : G.NonVerticialBranch)
    (coincidence :
      H.coincidence (map.edgeMap branch.1.1)
        (map.branchEquiv branch.1.1 branch.1.2) = none) :
    map.compactVertexMap (Sum.inr branch) =
      Sum.inr ⟨map.totalBranchMap branch.1, coincidence⟩ := by
  rw [compactVertexMap]
  split
  next vertex vertexCoincidence =>
    have impossible : some vertex = (none : Option H.Vertex) :=
      vertexCoincidence.symm.trans coincidence
    cases impossible
  next _ => rfl

/-- The compactification morphism induced by a source semi-graph morphism. -/
def compactificationMap (map : G.Hom H) :
    G.compactification.Hom H.compactification where
  vertexMap := map.compactVertexMap
  edgeMap := map.edgeMap
  branchEquiv := map.branchEquiv
  map_coincidence := by
    intro edge branch vertex sourceCoincidence
    cases original : G.coincidence edge branch with
    | some sourceVertex =>
        have targetCoincidence :=
          map.map_coincidence edge branch sourceVertex original
        rw [G.compactification_coincidence_of_some original] at sourceCoincidence
        have vertex_eq := Option.some.inj sourceCoincidence
        subst vertex
        exact H.compactification_coincidence_of_some targetCoincidence
    | none =>
        rw [G.compactification_coincidence_of_none original] at sourceCoincidence
        have vertex_eq := Option.some.inj sourceCoincidence
        subst vertex
        cases target :
            H.coincidence (map.edgeMap edge) (map.branchEquiv edge branch) with
        | some targetVertex =>
            rw [map.compactVertexMap_boundary_of_some _ target]
            exact H.compactification_coincidence_of_some target
        | none =>
            rw [map.compactVertexMap_boundary_of_none _ target]
            exact H.compactification_coincidence_of_none target

@[simp]
theorem compactVertexMap_original (map : G.Hom H) (vertex : G.Vertex) :
    map.compactVertexMap (Sum.inl vertex) =
      Sum.inl (map.vertexMap vertex) :=
  rfl

/-- The induced compactification morphism extends the original morphism on
vertices. -/
theorem compactificationMap_vertexMap_original (map : G.Hom H)
    (vertex : G.Vertex) :
    map.compactificationMap.vertexMap (Sum.inl vertex) =
      Sum.inl (map.vertexMap vertex) :=
  rfl

end Hom

end SourceSemiGraph

end Iut
