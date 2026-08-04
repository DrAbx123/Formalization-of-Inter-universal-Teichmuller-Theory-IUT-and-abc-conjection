/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceCombinatorialUniversalCover
import Iut.Foundations.SourceFiniteSheetSemiGraphCover

/-!
# Lifting the universal semigraph cover through a sheet cover

A family of branch permutations defines a graph covering of a semigraph.
Every based reduced incidence path has a unique sheet lift, so the
combinatorial universal cover maps to that sheet cover after one initial
sheet is chosen.  This is the general path-lifting step used in the proof of
*Semi-graphs of Anabelioids*, Proposition 3.6(ii).
-/

namespace Iut

universe u

open SourceCombinatorialUniversalCover

namespace SourceFiniteSheetSemiGraphCover

variable (base : SourceSemiGraph.{u}) (Sheet : Type u)
    (transport : ∀ edge : base.Edge, base.Branch edge → Equiv.Perm Sheet)

noncomputable section

/-- Lift an incidence node, measuring sheets at vertex nodes after branch
transport and at edge and branch nodes before branch transport. -/
def liftIncidenceNode :
    IncidenceNode base → Sheet → IncidenceNode (cover base Sheet transport)
  | .vertex (.inl vertex), sheet =>
      .vertex (.inl (vertex, sheet))
  | .vertex (.inr branch), sheet =>
      .vertex (.inr ⟨
        ⟨(branch.1.1,
          (transport branch.1.1 branch.1.2).symm sheet), branch.1.2⟩,
        by
          have branchNone :
              base.coincidence branch.1.1 branch.1.2 = none :=
            branch.2
          change Option.map _
            (base.coincidence branch.1.1 branch.1.2) = none
          rw [branchNone]
          rfl⟩)
  | .edge edge, sheet =>
      .edge (edge, sheet)
  | .branch branch, sheet =>
      .branch ⟨(branch.1, sheet), branch.2⟩

/-- Forgetting the lifted sheet recovers the original incidence node. -/
@[simp]
theorem properMap_liftIncidenceNode
    (node : IncidenceNode base) (sheet : Sheet) :
    IncidenceNode.properMap (cover base Sheet transport)
        (projection base Sheet transport)
        (projection_isGraphCovering base Sheet transport).1
        (liftIncidenceNode base Sheet transport node sheet) = node := by
  cases node with
  | vertex vertex =>
      cases vertex with
      | inl vertex => rfl
      | inr branch =>
          rw [liftIncidenceNode]
          rw [IncidenceNode.properMap_vertex_boundary]
          congr 3
  | edge edge => rfl
  | branch branch => rfl

/-- Sheet transport along one oriented incidence edge. -/
def incidenceStepTransport
    {first second : IncidenceNode base}
    (_adjacent : (IncidenceNode.incidenceGraph base).Adj first second) :
    Equiv.Perm Sheet :=
  match first, second with
  | .branch branch, .vertex _ => transport branch.1 branch.2
  | .vertex _, .branch branch => (transport branch.1 branch.2).symm
  | _, _ => Equiv.refl Sheet

/-- Reversing an incidence step inverts its sheet transport. -/
theorem incidenceStepTransport_reverse
    {first second : IncidenceNode base}
    (adjacent : (IncidenceNode.incidenceGraph base).Adj first second) :
    incidenceStepTransport base Sheet transport adjacent.symm =
      (incidenceStepTransport base Sheet transport adjacent).symm := by
  cases first <;> cases second <;>
    simp [incidenceStepTransport, IncidenceNode.incidenceGraph,
      IncidenceNode.incidenceRel, SimpleGraph.fromRel_adj] at adjacent ⊢

@[simp]
theorem incidenceStepTransport_edge_branch
    (branch : base.TotalBranch)
    (adjacent : (IncidenceNode.incidenceGraph base).Adj
      (.edge branch.1) (.branch branch)) :
    incidenceStepTransport base Sheet transport adjacent = Equiv.refl Sheet :=
  rfl

@[simp]
theorem incidenceStepTransport_branch_vertex
    (branch : base.TotalBranch) (vertex : base.CompactVertex)
    (adjacent : (IncidenceNode.incidenceGraph base).Adj
      (.branch branch) (.vertex vertex)) :
    incidenceStepTransport base Sheet transport adjacent =
      transport branch.1 branch.2 :=
  rfl

/-- The positive edge-to-branch half-step does not change sheets. -/
theorem liftIncidenceNode_edge_branch_adj
    (branch : base.TotalBranch) (sheet : Sheet) :
    (IncidenceNode.incidenceGraph (cover base Sheet transport)).Adj
      (liftIncidenceNode base Sheet transport (.edge branch.1) sheet)
      (liftIncidenceNode base Sheet transport (.branch branch) sheet) := by
  simp only [liftIncidenceNode]
  rw [IncidenceNode.edge_branch_adj]
  rfl

/-- The positive branch-to-vertex half-step applies its branch transport. -/
theorem liftIncidenceNode_branch_vertex_adj
    (branch : base.TotalBranch) (sheet : Sheet) :
    (IncidenceNode.incidenceGraph (cover base Sheet transport)).Adj
      (liftIncidenceNode base Sheet transport (.branch branch) sheet)
      (liftIncidenceNode base Sheet transport
        (.vertex (SourceSemiGraphUniversalCover.compactEndpoint
          base branch.1 branch.2))
        (transport branch.1 branch.2 sheet)) := by
  cases coincidence : base.coincidence branch.1 branch.2 with
  | some vertex =>
      rw [SourceSemiGraphUniversalCover.compactEndpoint_of_some
        base coincidence]
      simp only [liftIncidenceNode]
      rw [IncidenceNode.branch_vertex_adj]
      exact (cover base Sheet transport).compactification_coincidence_of_some
        (by
          change Option.map _ (base.coincidence branch.1 branch.2) = _
          rw [coincidence]
          rfl)
  | none =>
      have compactEndpoint :
          SourceSemiGraphUniversalCover.compactEndpoint
              base branch.1 branch.2 =
            Sum.inr ⟨branch, coincidence⟩ := by
        apply Option.some.inj
        rw [← SourceSemiGraphUniversalCover.compactEndpoint_spec]
        exact base.compactification_coincidence_of_none coincidence
      rw [compactEndpoint]
      simp only [liftIncidenceNode]
      rw [IncidenceNode.branch_vertex_adj]
      have coverNone :
          (cover base Sheet transport).coincidence
              (branch.1, sheet) branch.2 = none := by
        change Option.map _ (base.coincidence branch.1 branch.2) = none
        rw [coincidence]
        rfl
      rw [(cover base Sheet transport).compactification_coincidence_of_none
        coverNone]
      congr 5
      exact (Equiv.symm_apply_apply _ _).symm

/-- Every oriented base-incidence step has the advertised lifted endpoint. -/
theorem liftIncidenceNode_adj
    {first second : IncidenceNode base}
    (adjacent : (IncidenceNode.incidenceGraph base).Adj first second)
    (sheet : Sheet) :
    (IncidenceNode.incidenceGraph (cover base Sheet transport)).Adj
      (liftIncidenceNode base Sheet transport first sheet)
      (liftIncidenceNode base Sheet transport second
        (incidenceStepTransport base Sheet transport adjacent sheet)) := by
  cases first with
  | vertex point =>
      cases second with
      | vertex other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | edge edge =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | branch branch =>
          have endpoint :=
            (IncidenceNode.vertex_branch_adj base point branch).mp adjacent
          have pointEquality : point =
              SourceSemiGraphUniversalCover.compactEndpoint
                base branch.1 branch.2 :=
            Option.some.inj <| endpoint.symm.trans
              (SourceSemiGraphUniversalCover.compactEndpoint_spec
                base branch.1 branch.2)
          subst point
          simpa only [incidenceStepTransport, liftIncidenceNode,
            Equiv.apply_symm_apply] using
              (liftIncidenceNode_branch_vertex_adj
                base Sheet transport branch
                  ((transport branch.1 branch.2).symm sheet)).symm
  | edge edge =>
      cases second with
      | vertex point =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | edge other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent
      | branch branch =>
          have support :=
            (IncidenceNode.edge_branch_adj base edge branch).mp adjacent
          rcases branch with ⟨branchEdge, branch⟩
          change branchEdge = edge at support
          subst branchEdge
          simpa only [incidenceStepTransport, Equiv.refl_apply] using
            liftIncidenceNode_edge_branch_adj base Sheet transport
              (⟨edge, branch⟩ : base.TotalBranch) sheet
  | branch branch =>
      cases second with
      | vertex point =>
          have endpoint :=
            (IncidenceNode.branch_vertex_adj base branch point).mp adjacent
          have pointEquality : point =
              SourceSemiGraphUniversalCover.compactEndpoint
                base branch.1 branch.2 :=
            Option.some.inj <| endpoint.symm.trans
              (SourceSemiGraphUniversalCover.compactEndpoint_spec
                base branch.1 branch.2)
          subst point
          simpa only [incidenceStepTransport] using
            liftIncidenceNode_branch_vertex_adj
              base Sheet transport branch sheet
      | edge edge =>
          have support :=
            (IncidenceNode.branch_edge_adj base branch edge).mp adjacent
          rcases branch with ⟨branchEdge, branch⟩
          change branchEdge = edge at support
          subst branchEdge
          simpa only [incidenceStepTransport, Equiv.refl_apply] using
            (liftIncidenceNode_edge_branch_adj base Sheet transport
              (⟨edge, branch⟩ : base.TotalBranch) sheet).symm
      | branch other =>
          simp [IncidenceNode.incidenceGraph, IncidenceNode.incidenceRel,
            SimpleGraph.fromRel_adj] at adjacent

/-- Evaluate the branch transports along a reduced incidence walk. -/
def walkSheet :
    {pathRoot : IncidenceNode base} →
    {pathPrevious : Option (IncidenceNode base)} →
    {pathCurrent : IncidenceNode base} →
    ReducedWalk (IncidenceNode.incidenceGraph base)
        pathRoot pathPrevious pathCurrent → Sheet → Sheet
  | _, _, _, .nil, initial => initial
  | _, _, _, .step path adjacent _notBacktrack, initial =>
      incidenceStepTransport base Sheet transport adjacent
        (walkSheet path initial)

@[simp]
theorem walkSheet_nil
    (pathRoot : IncidenceNode base) (initial : Sheet) :
    walkSheet base Sheet transport
      (ReducedWalk.nil
        (graph := IncidenceNode.incidenceGraph base) (root := pathRoot))
      initial = initial :=
  by simp [walkSheet]

@[simp]
theorem walkSheet_step
    {pathRoot : IncidenceNode base}
    {pathPrevious : Option (IncidenceNode base)}
    {pathCurrent pathNext : IncidenceNode base}
    (path : ReducedWalk (IncidenceNode.incidenceGraph base)
      pathRoot pathPrevious pathCurrent)
    (adjacent :
      (IncidenceNode.incidenceGraph base).Adj pathCurrent pathNext)
    (notBacktrack : pathPrevious ≠ some pathNext)
    (initial : Sheet) :
    walkSheet base Sheet transport (.step path adjacent notBacktrack) initial =
      incidenceStepTransport base Sheet transport adjacent
        (walkSheet base Sheet transport path initial) :=
  by simp [walkSheet]

/-- The sheet reached by the reduced path represented by a universal-tree
vertex. -/
def universalVertexSheet
    {root : IncidenceNode base}
    (point : UniversalVertex (IncidenceNode.incidenceGraph base) root)
    (initial : Sheet) : Sheet :=
  walkSheet base Sheet transport point.walk initial

/-- A child universal vertex advances the sheet by its last incidence step. -/
theorem universalVertexSheet_of_parent
    {root : IncidenceNode base}
    {first second : UniversalVertex (IncidenceNode.incidenceGraph base) root}
    (parent : second.parent = some first) (initial : Sheet) :
    universalVertexSheet base Sheet transport second initial =
      incidenceStepTransport base Sheet transport
        (UniversalVertex.endpoint_adj_of_parent _ _ parent)
        (universalVertexSheet base Sheet transport first initial) := by
  rcases second with ⟨previous, current, walk⟩
  cases walk with
  | nil => simp [UniversalVertex.parent] at parent
  | @step before prior current path adjacent notBacktrack =>
      let endpointAdjacent := UniversalVertex.endpoint_adj_of_parent
        (IncidenceNode.incidenceGraph base) _ parent
      simp only [UniversalVertex.parent, Option.some.injEq] at parent
      cases parent
      change
        universalVertexSheet base Sheet transport
            ⟨some prior, current, .step path adjacent notBacktrack⟩ initial =
          incidenceStepTransport base Sheet transport endpointAdjacent
            (universalVertexSheet base Sheet transport
              ⟨before, prior, path⟩ initial)
      have endpointAdjacent_eq : endpointAdjacent = adjacent :=
        Subsingleton.elim _ _
      rw [endpointAdjacent_eq]
      simp only [universalVertexSheet]
      rw [walkSheet_step]
      rfl

/-- Adjacent universal-tree vertices have sheets related by the corresponding
oriented base-incidence transport. -/
theorem universalVertexSheet_adj
    {root : IncidenceNode base}
    {first second : UniversalVertex (IncidenceNode.incidenceGraph base) root}
    (adjacent : (UniversalVertex.tree
      (IncidenceNode.incidenceGraph base) root).Adj first second)
    (initial : Sheet) :
    universalVertexSheet base Sheet transport second initial =
      incidenceStepTransport base Sheet transport
        (UniversalVertex.endpoint_adj _ _ adjacent)
        (universalVertexSheet base Sheet transport first initial) := by
  rcases (UniversalVertex.tree_adj_iff
    (graph := IncidenceNode.incidenceGraph base) (root := root)).mp adjacent with
    ⟨_, secondChild | firstChild⟩
  · exact universalVertexSheet_of_parent
      base Sheet transport secondChild initial
  · have reverse := universalVertexSheet_of_parent
      base Sheet transport firstChild initial
    let backward := UniversalVertex.endpoint_adj_of_parent
      (IncidenceNode.incidenceGraph base) root firstChild
    calc
      universalVertexSheet base Sheet transport second initial =
          (incidenceStepTransport base Sheet transport backward).symm
            (incidenceStepTransport base Sheet transport backward
              (universalVertexSheet base Sheet transport second initial)) :=
        (Equiv.symm_apply_apply _ _).symm
      _ = (incidenceStepTransport base Sheet transport backward).symm
            (universalVertexSheet base Sheet transport first initial) :=
        congrArg _ reverse.symm
      _ = incidenceStepTransport base Sheet transport
            (UniversalVertex.endpoint_adj _ _ adjacent)
            (universalVertexSheet base Sheet transport first initial) := by
        rw [← incidenceStepTransport_reverse
          base Sheet transport backward]

namespace UniversalLift

variable (root : base.Vertex) (initial : Sheet)

/-- Lifted universal vertices with their path-evaluated sheet. -/
def vertexMap
    (vertex : SourceSemiGraphUniversalCover.LiftedVertex base root) :
    (cover base Sheet transport).Vertex :=
  (vertex.vertex,
    universalVertexSheet base Sheet transport vertex.path initial)

/-- Lifted universal edges with their path-evaluated sheet. -/
def edgeMap
    (edge : SourceSemiGraphUniversalCover.LiftedEdge base root) :
    (cover base Sheet transport).Edge :=
  (edge.edge,
    universalVertexSheet base Sheet transport edge.path initial)

/-- The lifted sheet at a coincident universal vertex is the branch transport
of the lifted sheet at its edge. -/
theorem vertexSheet_eq_transport_of_coincidence
    (edge : SourceSemiGraphUniversalCover.LiftedEdge base root)
    (branch : base.Branch edge.edge)
    (vertex : SourceSemiGraphUniversalCover.LiftedVertex base root)
    (coincidence :
      (SourceSemiGraphUniversalCover.semiGraphCover base root).coincidence
        edge branch = some vertex) :
    universalVertexSheet base Sheet transport vertex.path initial =
      transport edge.edge branch
        (universalVertexSheet base Sheet transport edge.path initial) := by
  have pathEquality :=
    SourceSemiGraphUniversalCover.compactVertexPath_eq_of_coincidence
      base root edge branch vertex coincidence
  rw [← pathEquality]
  let branchPath := SourceSemiGraphUniversalCover.branchPath
    base root edge branch
  have edgeAdjacent :
      (UniversalVertex.tree (IncidenceNode.incidenceGraph base)
        (SourceSemiGraphUniversalCover.incidenceRoot base root)).Adj
          edge.path branchPath :=
    UniversalVertex.adjacent_liftNeighbor _ _ _ _ _
  have vertexAdjacent :
      (UniversalVertex.tree (IncidenceNode.incidenceGraph base)
        (SourceSemiGraphUniversalCover.incidenceRoot base root)).Adj
          branchPath
          (SourceSemiGraphUniversalCover.compactVertexPath
            base root edge branch) :=
    UniversalVertex.adjacent_liftNeighbor _ _ _ _ _
  rw [universalVertexSheet_adj
    base Sheet transport vertexAdjacent initial]
  rw [universalVertexSheet_adj
    base Sheet transport edgeAdjacent initial]
  have vertexTransport :
      incidenceStepTransport base Sheet transport
          (UniversalVertex.endpoint_adj _ _ vertexAdjacent) =
        transport edge.edge branch := by
    let explicitAdjacent : (IncidenceNode.incidenceGraph base).Adj
        (.branch (⟨edge.edge, branch⟩ : base.TotalBranch))
        (.vertex (SourceSemiGraphUniversalCover.compactEndpoint
          base edge.edge branch)) := by
      rw [IncidenceNode.branch_vertex_adj]
      exact SourceSemiGraphUniversalCover.compactEndpoint_spec
        base edge.edge branch
    simpa only [branchPath, SourceSemiGraphUniversalCover.branchPath,
      UniversalVertex.liftNeighbor_endpoint,
      SourceSemiGraphUniversalCover.compactVertexPath_endpoint] using
        incidenceStepTransport_branch_vertex base Sheet transport
          (⟨edge.edge, branch⟩ : base.TotalBranch)
          (SourceSemiGraphUniversalCover.compactEndpoint
            base edge.edge branch) explicitAdjacent
  have edgeTransport :
      incidenceStepTransport base Sheet transport
          (UniversalVertex.endpoint_adj _ _ edgeAdjacent) =
        Equiv.refl Sheet := by
    let explicitAdjacent : (IncidenceNode.incidenceGraph base).Adj
        (.edge edge.edge)
        (.branch (⟨edge.edge, branch⟩ : base.TotalBranch)) := by
      rw [IncidenceNode.edge_branch_adj]
      rfl
    simpa only [edge.endpoint_eq, branchPath,
      SourceSemiGraphUniversalCover.branchPath,
      UniversalVertex.liftNeighbor_endpoint] using
        incidenceStepTransport_edge_branch base Sheet transport
          (⟨edge.edge, branch⟩ : base.TotalBranch) explicitAdjacent
  rw [vertexTransport, edgeTransport]
  rfl

/-- The based lift from the combinatorial universal cover to a branch-sheet
cover. -/
def hom :
    (SourceSemiGraphUniversalCover.semiGraphCover base root).Hom
      (cover base Sheet transport) where
  vertexMap := vertexMap base Sheet transport root initial
  edgeMap := edgeMap base Sheet transport root initial
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro edge branch vertex coincidence
    have sourceCoincidence :
        base.coincidence edge.edge branch = some vertex.vertex :=
      (SourceSemiGraphUniversalCover.projection base root).map_coincidence
        edge branch vertex coincidence
    change Option.map
        (fun target => (target,
          transport edge.edge branch
            (universalVertexSheet base Sheet transport edge.path initial)))
        (base.coincidence edge.edge branch) =
      some (vertex.vertex,
        universalVertexSheet base Sheet transport vertex.path initial)
    rw [sourceCoincidence]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
    exact (vertexSheet_eq_transport_of_coincidence
      base Sheet transport root initial edge branch vertex coincidence).symm

/-- The universal lift lies over the original universal projection. -/
theorem projection_comp_hom :
    (hom base Sheet transport root initial).comp
        (projection base Sheet transport) =
      SourceSemiGraphUniversalCover.projection base root := by
  apply SourceSemiGraph.Hom.ext
  · intro vertex
    rfl
  · intro edge
    rfl
  · intro edge branch
    rfl

end UniversalLift

end

end SourceFiniteSheetSemiGraphCover

end Iut
