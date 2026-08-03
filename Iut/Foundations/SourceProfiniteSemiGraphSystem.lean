/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceProfiniteCosetSystem

/-!
# Normal-open finite levels of a subgroup semi-graph

This module assembles the separate constituent coset systems from
`SourceProfiniteCosetSystem` into the finite-level semi-graphs of the
normal-open pro-system in *Semi-graphs of Anabelioids*, Remark 2.2.1.  Normality
is used to extend every branch transport from `H_e` to `H_e sup N`, and the
quotient maps for `N <= M` are proved compatible with all coincidence maps.
-/

namespace Iut

universe u

open CategoryTheory QuotientGroup

namespace SourceSemiGraphSubgroupDiagram

variable {Ambient : Type u} [Group Ambient] [TopologicalSpace Ambient]
    (diagram : SourceSemiGraphSubgroupDiagram.{u} Ambient)

/-- Enlarge every constituent subgroup by an open normal subgroup of the
ambient group. -/
def normalOpenLevel (N : OpenNormalSubgroup Ambient) :
    SourceSemiGraphSubgroupDiagram Ambient where
  base := diagram.base
  vertexGroup vertex := diagram.vertexGroup vertex ⊔ N.toSubgroup
  edgeGroup edge := diagram.edgeGroup edge ⊔ N.toSubgroup
  branchTransport := fun {edge} branch {vertex} abuts =>
    diagram.branchTransport (edge := edge) branch (vertex := vertex) abuts
  transport_compatible := by
    intro edge branch vertex abuts value value_mem
    rcases Subgroup.mem_sup_of_normal_right.mp value_mem with
      ⟨edgeValue, edgeValue_mem, normalValue, normalValue_mem, rfl⟩
    have edgeTransported :=
      diagram.transport_compatible branch abuts edgeValue edgeValue_mem
    have normalTransported :=
      N.isNormal'.conj_mem' normalValue normalValue_mem
        (diagram.branchTransport branch abuts)
    have product_mem :=
      Subgroup.mul_mem_sup edgeTransported normalTransported
    convert product_mem using 1
    group

/-- The finite-level coset semi-graph attached to an open normal subgroup. -/
def normalOpenLevelSemiGraph (N : OpenNormalSubgroup Ambient) :
    SourceSemiGraph :=
  (diagram.normalOpenLevel N).cosetSemiGraph

/-- Forget the normal-open coset coordinate and return to the source
semi-graph. -/
def normalOpenLevelProjection (N : OpenNormalSubgroup Ambient) :
    (diagram.normalOpenLevelSemiGraph N).Hom diagram.base where
  vertexMap := Sigma.fst
  edgeMap := Sigma.fst
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    rintro ⟨edge, coset⟩ branch ⟨vertex, vertexCoset⟩ coincidence
    change (diagram.normalOpenLevel N).cosetSemiGraph.coincidence
      ⟨edge, coset⟩ branch = some ⟨vertex, vertexCoset⟩ at coincidence
    change diagram.base.coincidence edge branch = some vertex
    cases abutment : diagram.base.coincidence edge branch with
    | none =>
        rw [(diagram.normalOpenLevel N).cosetSemiGraph_coincidence_of_none
          (edge := ⟨edge, coset⟩) (branch := branch) abutment] at coincidence
        cases coincidence
    | some target =>
        rw [(diagram.normalOpenLevel N).cosetSemiGraph_coincidence_of_some
          (edge := ⟨edge, coset⟩) (branch := branch) abutment] at coincidence
        have vertexEquality : target = vertex :=
          congrArg Sigma.fst (Option.some.inj coincidence)
        exact congrArg some vertexEquality

/-- The level projection preserves and reflects whether a branch is
verticial. -/
theorem normalOpenLevelProjection_isProper (N : OpenNormalSubgroup Ambient) :
    (diagram.normalOpenLevelProjection N).IsProper := by
  rintro ⟨edge, coset⟩ branch
  change
    (∃ vertex, (diagram.normalOpenLevel N).cosetSemiGraph.coincidence
      ⟨edge, coset⟩ branch = some vertex) ↔
    ∃ vertex, diagram.base.coincidence edge branch = some vertex
  cases abutment : diagram.base.coincidence edge branch with
  | none =>
      constructor
      · rintro ⟨vertex, coincidence⟩
        rw [(diagram.normalOpenLevel N).cosetSemiGraph_coincidence_of_none
          (edge := ⟨edge, coset⟩) (branch := branch) abutment] at coincidence
        cases coincidence
      · rintro ⟨vertex, coincidence⟩
        cases coincidence
  | some vertex =>
      constructor
      · intro _
        exact ⟨vertex, rfl⟩
      · intro _
        exact ⟨⟨vertex,
          (diagram.normalOpenLevel N).branchCosetMap branch abutment coset⟩,
          (diagram.normalOpenLevel N).cosetSemiGraph_coincidence_of_some
            (edge := ⟨edge, coset⟩) (branch := branch) abutment⟩

/-- Every vertex coset fiber at a normal-open level is finite. -/
theorem normalOpenLevel_vertexCoset_finite
    [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    (N : OpenNormalSubgroup Ambient) (vertex : diagram.base.Vertex) :
    Finite (Ambient ⧸ (diagram.normalOpenLevel N).vertexGroup vertex) :=
  SourceProfiniteCosetSystem.finite_level
    (diagram.vertexGroup vertex) N

/-- Every edge coset fiber at a normal-open level is finite. -/
theorem normalOpenLevel_edgeCoset_finite
    [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    (N : OpenNormalSubgroup Ambient) (edge : diagram.base.Edge) :
    Finite (Ambient ⧸ (diagram.normalOpenLevel N).edgeGroup edge) :=
  SourceProfiniteCosetSystem.finite_level
    (diagram.edgeGroup edge) N

/-- If the base has finitely many vertices, then so does every normal-open
coset level. -/
theorem normalOpenLevel_vertices_finite
    [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    [Finite diagram.base.Vertex] (N : OpenNormalSubgroup Ambient) :
    Finite (diagram.normalOpenLevelSemiGraph N).Vertex := by
  letI : Finite (diagram.normalOpenLevel N).base.Vertex :=
    inferInstanceAs (Finite diagram.base.Vertex)
  letI (vertex : (diagram.normalOpenLevel N).base.Vertex) :
      Finite (Ambient ⧸
        (diagram.normalOpenLevel N).vertexGroup vertex) :=
    diagram.normalOpenLevel_vertexCoset_finite N vertex
  change Finite (Σ vertex, Ambient ⧸
    (diagram.normalOpenLevel N).vertexGroup vertex)
  exact inferInstance

/-- If the base has finitely many edges, then so does every normal-open coset
level. -/
theorem normalOpenLevel_edges_finite
    [IsTopologicalGroup Ambient] [CompactSpace Ambient]
    [Finite diagram.base.Edge] (N : OpenNormalSubgroup Ambient) :
    Finite (diagram.normalOpenLevelSemiGraph N).Edge := by
  letI : Finite (diagram.normalOpenLevel N).base.Edge :=
    inferInstanceAs (Finite diagram.base.Edge)
  letI (edge : (diagram.normalOpenLevel N).base.Edge) :
      Finite (Ambient ⧸ (diagram.normalOpenLevel N).edgeGroup edge) :=
    diagram.normalOpenLevel_edgeCoset_finite N edge
  change Finite (Σ edge, Ambient ⧸
    (diagram.normalOpenLevel N).edgeGroup edge)
  exact inferInstance

/-- Quotient a finite-level vertex along an inclusion of open normal
subgroups. -/
def normalOpenLevelVertexMap {N M : OpenNormalSubgroup Ambient}
    (map : N ⟶ M) :
    (diagram.normalOpenLevel N).CosetVertex →
      (diagram.normalOpenLevel M).CosetVertex
  | ⟨vertex, coset⟩ =>
      ⟨vertex, Subgroup.quotientMapOfLE
        (SourceProfiniteCosetSystem.levelSubgroup_mono
          (diagram.vertexGroup vertex) map) coset⟩

/-- Quotient a finite-level edge along an inclusion of open normal
subgroups. -/
def normalOpenLevelEdgeMap {N M : OpenNormalSubgroup Ambient}
    (map : N ⟶ M) :
    (diagram.normalOpenLevel N).CosetEdge →
      (diagram.normalOpenLevel M).CosetEdge
  | ⟨edge, coset⟩ =>
      ⟨edge, Subgroup.quotientMapOfLE
        (SourceProfiniteCosetSystem.levelSubgroup_mono
          (diagram.edgeGroup edge) map) coset⟩

/-- Branch incidence commutes with the quotient map from level `N` to level
`M`. -/
theorem normalOpenLevel_branchCosetMap_transition
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M)
    {edge : diagram.base.Edge} (branch : diagram.base.Branch edge)
    {vertex : diagram.base.Vertex}
    (abuts : diagram.base.coincidence edge branch = some vertex)
    (coset : Ambient ⧸
      (diagram.normalOpenLevel N).edgeGroup edge) :
    Subgroup.quotientMapOfLE
        (SourceProfiniteCosetSystem.levelSubgroup_mono
          (diagram.vertexGroup vertex) map)
        ((diagram.normalOpenLevel N).branchCosetMap branch abuts coset) =
      (diagram.normalOpenLevel M).branchCosetMap branch abuts
        (Subgroup.quotientMapOfLE
          (SourceProfiniteCosetSystem.levelSubgroup_mono
            (diagram.edgeGroup edge) map) coset) := by
  induction coset using Quotient.inductionOn'
  rfl

/-- The semi-graph morphism between normal-open levels induced by `N <= M`. -/
def normalOpenLevelTransition {N M : OpenNormalSubgroup Ambient}
    (map : N ⟶ M) :
    (diagram.normalOpenLevelSemiGraph N).Hom
      (diagram.normalOpenLevelSemiGraph M) where
  vertexMap := diagram.normalOpenLevelVertexMap map
  edgeMap := diagram.normalOpenLevelEdgeMap map
  branchEquiv := fun ⟨edge, _⟩ => Equiv.refl (diagram.base.Branch edge)
  map_coincidence := by
    rintro ⟨edge, edgeCoset⟩ branch ⟨vertex, vertexCoset⟩ coincidence
    change (diagram.normalOpenLevel N).cosetSemiGraph.coincidence
      ⟨edge, edgeCoset⟩ branch = some ⟨vertex, vertexCoset⟩ at coincidence
    change (diagram.normalOpenLevel M).cosetSemiGraph.coincidence
      (diagram.normalOpenLevelEdgeMap map ⟨edge, edgeCoset⟩) branch =
        some (diagram.normalOpenLevelVertexMap map ⟨vertex, vertexCoset⟩)
    cases abutment : diagram.base.coincidence edge branch with
    | none =>
        rw [(diagram.normalOpenLevel N).cosetSemiGraph_coincidence_of_none
          (edge := ⟨edge, edgeCoset⟩) (branch := branch) abutment]
          at coincidence
        cases coincidence
    | some abuttingVertex =>
        rw [(diagram.normalOpenLevel N).cosetSemiGraph_coincidence_of_some
          (edge := ⟨edge, edgeCoset⟩) (branch := branch)
          (vertex := abuttingVertex) abutment] at coincidence
        have componentEquality := Option.some.inj coincidence
        cases componentEquality
        rw [(diagram.normalOpenLevel M).cosetSemiGraph_coincidence_of_some
          (edge := diagram.normalOpenLevelEdgeMap map ⟨edge, edgeCoset⟩)
          (branch := branch) (vertex := vertex) abutment]
        apply congrArg some
        change (⟨vertex, _⟩ :
          (diagram.normalOpenLevel M).CosetVertex) = ⟨vertex, _⟩
        refine Sigma.ext rfl ?_
        exact heq_of_eq
          (diagram.normalOpenLevel_branchCosetMap_transition
            map branch abutment edgeCoset).symm

/-- Identity transition on finite-level vertices. -/
theorem normalOpenLevelVertexMap_id (N : OpenNormalSubgroup Ambient)
    (point : (diagram.normalOpenLevel N).CosetVertex) :
    diagram.normalOpenLevelVertexMap (𝟙 N) point = point := by
  rcases point with ⟨vertex, coset⟩
  change (⟨vertex, _⟩ : (diagram.normalOpenLevel N).CosetVertex) =
    ⟨vertex, coset⟩
  refine Sigma.ext rfl ?_
  induction coset using Quotient.inductionOn'
  rfl

/-- Identity transition on finite-level edges. -/
theorem normalOpenLevelEdgeMap_id (N : OpenNormalSubgroup Ambient)
    (point : (diagram.normalOpenLevel N).CosetEdge) :
    diagram.normalOpenLevelEdgeMap (𝟙 N) point = point := by
  rcases point with ⟨edge, coset⟩
  change (⟨edge, _⟩ : (diagram.normalOpenLevel N).CosetEdge) =
    ⟨edge, coset⟩
  refine Sigma.ext rfl ?_
  induction coset using Quotient.inductionOn'
  rfl

/-- Composition law for finite-level vertex transitions. -/
theorem normalOpenLevelVertexMap_comp
    {N M L : OpenNormalSubgroup Ambient} (first : N ⟶ M)
    (second : M ⟶ L)
    (point : (diagram.normalOpenLevel N).CosetVertex) :
    diagram.normalOpenLevelVertexMap (first ≫ second) point =
      diagram.normalOpenLevelVertexMap second
        (diagram.normalOpenLevelVertexMap first point) := by
  rcases point with ⟨vertex, coset⟩
  change (⟨vertex, _⟩ : (diagram.normalOpenLevel L).CosetVertex) =
    ⟨vertex, _⟩
  refine Sigma.ext rfl ?_
  induction coset using Quotient.inductionOn'
  rfl

/-- Composition law for finite-level edge transitions. -/
theorem normalOpenLevelEdgeMap_comp
    {N M L : OpenNormalSubgroup Ambient} (first : N ⟶ M)
    (second : M ⟶ L)
    (point : (diagram.normalOpenLevel N).CosetEdge) :
    diagram.normalOpenLevelEdgeMap (first ≫ second) point =
      diagram.normalOpenLevelEdgeMap second
        (diagram.normalOpenLevelEdgeMap first point) := by
  rcases point with ⟨edge, coset⟩
  change (⟨edge, _⟩ : (diagram.normalOpenLevel L).CosetEdge) =
    ⟨edge, _⟩
  refine Sigma.ext rfl ?_
  induction coset using Quotient.inductionOn'
  rfl

/-- Every coarser-level vertex has a lift to a finer normal-open level. -/
theorem normalOpenLevelVertexMap_surjective
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M) :
    Function.Surjective (diagram.normalOpenLevelVertexMap map) := by
  rintro ⟨vertex, coset⟩
  induction coset using Quotient.inductionOn'
  exact ⟨⟨vertex, QuotientGroup.mk _⟩, rfl⟩

/-- Every coarser-level edge has a lift to a finer normal-open level. -/
theorem normalOpenLevelEdgeMap_surjective
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M) :
    Function.Surjective (diagram.normalOpenLevelEdgeMap map) := by
  rintro ⟨edge, coset⟩
  induction coset using Quotient.inductionOn'
  exact ⟨⟨edge, QuotientGroup.mk _⟩, rfl⟩

/-- Vertex transition maps are equivariant for the ambient deck action. -/
theorem normalOpenLevelVertexMap_action
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M)
    (g : Ambient)
    (point : (diagram.normalOpenLevel N).CosetVertex) :
    diagram.normalOpenLevelVertexMap map
        ((diagram.normalOpenLevel N).cosetAction.vertexAction g point) =
      (diagram.normalOpenLevel M).cosetAction.vertexAction g
        (diagram.normalOpenLevelVertexMap map point) := by
  rcases point with ⟨vertex, coset⟩
  change (⟨vertex, _⟩ : (diagram.normalOpenLevel M).CosetVertex) =
    ⟨vertex, _⟩
  refine Sigma.ext rfl ?_
  induction coset using Quotient.inductionOn'
  rfl

/-- Edge transition maps are equivariant for the ambient deck action. -/
theorem normalOpenLevelEdgeMap_action
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M)
    (g : Ambient)
    (point : (diagram.normalOpenLevel N).CosetEdge) :
    diagram.normalOpenLevelEdgeMap map
        ((diagram.normalOpenLevel N).cosetAction.edgeAction g point) =
      (diagram.normalOpenLevel M).cosetAction.edgeAction g
        (diagram.normalOpenLevelEdgeMap map point) := by
  rcases point with ⟨edge, coset⟩
  change (⟨edge, _⟩ : (diagram.normalOpenLevel M).CosetEdge) =
    ⟨edge, _⟩
  refine Sigma.ext rfl ?_
  induction coset using Quotient.inductionOn'
  rfl

/-- Identity transition on total branches. -/
theorem normalOpenLevelTransition_totalBranchMap_id
    (N : OpenNormalSubgroup Ambient)
    (branch : (diagram.normalOpenLevelSemiGraph N).TotalBranch) :
    (diagram.normalOpenLevelTransition (𝟙 N)).totalBranchMap branch =
      branch := by
  rcases branch with ⟨⟨edge, coset⟩, branch⟩
  induction coset using Quotient.inductionOn'
  rfl

/-- Composition law for transition maps on total branches. -/
theorem normalOpenLevelTransition_totalBranchMap_comp
    {N M L : OpenNormalSubgroup Ambient} (first : N ⟶ M)
    (second : M ⟶ L)
    (branch : (diagram.normalOpenLevelSemiGraph N).TotalBranch) :
    (diagram.normalOpenLevelTransition (first ≫ second)).totalBranchMap branch =
      (diagram.normalOpenLevelTransition second).totalBranchMap
        ((diagram.normalOpenLevelTransition first).totalBranchMap branch) := by
  rcases branch with ⟨⟨edge, coset⟩, branch⟩
  induction coset using Quotient.inductionOn'
  rfl

/-- Every coarser-level total branch has a lift to a finer normal-open level. -/
theorem normalOpenLevelTransition_totalBranchMap_surjective
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M) :
    Function.Surjective
      (diagram.normalOpenLevelTransition map).totalBranchMap := by
  rintro ⟨⟨edge, coset⟩, branch⟩
  induction coset using Quotient.inductionOn'
  exact ⟨⟨⟨edge, QuotientGroup.mk _⟩, branch⟩, rfl⟩

/-- Transition maps on total branches are equivariant for the ambient deck
action. -/
theorem normalOpenLevelTransition_totalBranchMap_action
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M)
    (g : Ambient)
    (branch : (diagram.normalOpenLevelSemiGraph N).TotalBranch) :
    (diagram.normalOpenLevelTransition map).totalBranchMap
        ((diagram.normalOpenLevel N).cosetAction.branchAction g branch) =
      (diagram.normalOpenLevel M).cosetAction.branchAction g
        ((diagram.normalOpenLevelTransition map).totalBranchMap branch) := by
  rcases branch with ⟨⟨edge, coset⟩, branch⟩
  induction coset using Quotient.inductionOn'
  rfl

/-- Normal-open transition maps preserve both verticial and nonverticial
branches. -/
theorem normalOpenLevelTransition_isProper
    {N M : OpenNormalSubgroup Ambient} (map : N ⟶ M) :
    (diagram.normalOpenLevelTransition map).IsProper := by
  rintro ⟨edge, edgeCoset⟩ branch
  cases abutment : diagram.base.coincidence edge branch with
  | none =>
      constructor
      · rintro ⟨vertex, coincidence⟩
        change (diagram.normalOpenLevel N).cosetSemiGraph.coincidence
          ⟨edge, edgeCoset⟩ branch = some vertex at coincidence
        rw [(diagram.normalOpenLevel N).cosetSemiGraph_coincidence_of_none
          (edge := ⟨edge, edgeCoset⟩) (branch := branch) abutment]
          at coincidence
        cases coincidence
      · rintro ⟨vertex, coincidence⟩
        change (diagram.normalOpenLevel M).cosetSemiGraph.coincidence
          (diagram.normalOpenLevelEdgeMap map ⟨edge, edgeCoset⟩) branch =
            some vertex at coincidence
        rw [(diagram.normalOpenLevel M).cosetSemiGraph_coincidence_of_none
          (edge := diagram.normalOpenLevelEdgeMap map ⟨edge, edgeCoset⟩)
          (branch := branch) abutment] at coincidence
        cases coincidence
  | some vertex =>
      constructor
      · intro _
        let targetEdge :=
          diagram.normalOpenLevelEdgeMap map ⟨edge, edgeCoset⟩
        refine ⟨⟨vertex,
          (diagram.normalOpenLevel M).branchCosetMap branch abutment
            targetEdge.2⟩, ?_⟩
        change (diagram.normalOpenLevel M).cosetSemiGraph.coincidence
          targetEdge branch = _
        exact (diagram.normalOpenLevel M).cosetSemiGraph_coincidence_of_some
          (edge := targetEdge) (branch := branch) abutment
      · intro _
        refine ⟨⟨vertex,
          (diagram.normalOpenLevel N).branchCosetMap branch abutment
            edgeCoset⟩, ?_⟩
        change (diagram.normalOpenLevel N).cosetSemiGraph.coincidence
          ⟨edge, edgeCoset⟩ branch = _
        exact (diagram.normalOpenLevel N).cosetSemiGraph_coincidence_of_some
          (edge := ⟨edge, edgeCoset⟩) (branch := branch) abutment

end SourceSemiGraphSubgroupDiagram

end Iut
