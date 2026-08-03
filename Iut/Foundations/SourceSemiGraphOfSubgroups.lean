/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Iut.Foundations.SourceSemiGraphAction

/-!
# Coset semi-graphs of subgroups

This module formalizes the Bass--Serre coset model underlying the stabilizer
identification in *Semi-graphs of Anabelioids*, Remark 2.2.1.  Lifted vertices
and edges are left cosets of their constituent subgroups.  A branch transport
element records the possible conjugation in its incidence map; this is
essential for loop edges and HNN-type graphs of groups.  The profinite
inverse-limit realization of the universal covering is a separate step.
-/

namespace Iut

universe u

open QuotientGroup

/-- A semi-graph whose vertex and edge groups have been embedded in a common
ambient group.  At an incident branch `b`, the transport element `tau` is
required to satisfy `tau^-1 * H_e * tau <= H_v`. -/
structure SourceSemiGraphSubgroupDiagram
    (Ambient : Type u) [Group Ambient] where
  base : SourceSemiGraph.{u}
  vertexGroup : base.Vertex → Subgroup Ambient
  edgeGroup : base.Edge → Subgroup Ambient
  branchTransport :
    ∀ {edge} (branch : base.Branch edge) {vertex},
      base.coincidence edge branch = some vertex → Ambient
  transport_compatible :
    ∀ {edge} (branch : base.Branch edge) {vertex}
      (abuts : base.coincidence edge branch = some vertex)
      (value : Ambient),
      value ∈ edgeGroup edge →
        (branchTransport branch abuts)⁻¹ * value *
            branchTransport branch abuts ∈
          vertexGroup vertex

namespace SourceSemiGraphSubgroupDiagram

variable {Ambient : Type u} [Group Ambient]
    (diagram : SourceSemiGraphSubgroupDiagram.{u} Ambient)

/-- Right multiplication by a branch transport gives the incidence map from
edge cosets to vertex cosets. -/
def branchCosetMap {edge : diagram.base.Edge}
    (branch : diagram.base.Branch edge) {vertex : diagram.base.Vertex}
    (abuts : diagram.base.coincidence edge branch = some vertex) :
    Ambient ⧸ diagram.edgeGroup edge → Ambient ⧸ diagram.vertexGroup vertex :=
  Quotient.map' (fun value => value * diagram.branchTransport branch abuts)
    fun first second relation => by
      rw [QuotientGroup.leftRel_apply]
      have source : first⁻¹ * second ∈ diagram.edgeGroup edge :=
        QuotientGroup.leftRel_apply.mp relation
      simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using
        diagram.transport_compatible branch abuts (first⁻¹ * second) source

/-- The branch coset incidence map is equivariant for left multiplication by
the ambient group. -/
theorem branchCosetMap_smul {edge : diagram.base.Edge}
    (branch : diagram.base.Branch edge) {vertex : diagram.base.Vertex}
    (abuts : diagram.base.coincidence edge branch = some vertex)
    (g : Ambient) (coset : Ambient ⧸ diagram.edgeGroup edge) :
    diagram.branchCosetMap branch abuts (g • coset) =
      g • diagram.branchCosetMap branch abuts coset := by
  induction coset using Quotient.inductionOn'
  simp [branchCosetMap, mul_assoc]

/-- Vertices in the coset semi-graph. -/
def CosetVertex :=
  Σ vertex, Ambient ⧸ diagram.vertexGroup vertex

/-- Edges in the coset semi-graph. -/
def CosetEdge :=
  Σ edge, Ambient ⧸ diagram.edgeGroup edge

/-- The coincidence map of the coset semi-graph. -/
def cosetCoincidence (edge : diagram.CosetEdge)
    (branch : diagram.base.Branch edge.1) : Option diagram.CosetVertex :=
  match abuts : diagram.base.coincidence edge.1 branch with
  | some vertex =>
      some ⟨vertex, diagram.branchCosetMap branch abuts edge.2⟩
  | none => none

/-- The coset semi-graph associated to a subgroup diagram. -/
def cosetSemiGraph : SourceSemiGraph.{u} where
  Vertex := diagram.CosetVertex
  Edge := diagram.CosetEdge
  Branch := fun edge => diagram.base.Branch edge.1
  branchFintype := fun edge => diagram.base.branchFintype edge.1
  branch_card := fun edge => diagram.base.branch_card edge.1
  coincidence := diagram.cosetCoincidence

@[simp]
theorem cosetSemiGraph_coincidence_of_some
    {edge : diagram.CosetEdge} {branch : diagram.base.Branch edge.1}
    {vertex : diagram.base.Vertex}
    (abuts : diagram.base.coincidence edge.1 branch = some vertex) :
    diagram.cosetSemiGraph.coincidence edge branch =
      some ⟨vertex, diagram.branchCosetMap branch abuts edge.2⟩ := by
  change diagram.cosetCoincidence edge branch = _
  unfold cosetCoincidence
  split
  next value value_abuts =>
    have value_eq : value = vertex :=
      Option.some.inj (value_abuts.symm.trans abuts)
    subst value
    rfl
  next no_abutment =>
    have impossible : (none : Option diagram.base.Vertex) = some vertex :=
      no_abutment.symm.trans abuts
    cases impossible

@[simp]
theorem cosetSemiGraph_coincidence_of_none
    {edge : diagram.CosetEdge} {branch : diagram.base.Branch edge.1}
    (no_abutment : diagram.base.coincidence edge.1 branch = none) :
    diagram.cosetSemiGraph.coincidence edge branch = none := by
  change diagram.cosetCoincidence edge branch = none
  unfold cosetCoincidence
  split
  next vertex abuts =>
    have impossible : some vertex = (none : Option diagram.base.Vertex) :=
      abuts.symm.trans no_abutment
    cases impossible
  next _ => rfl

/-- Left multiplication on coset vertices. -/
@[reducible] def cosetVertexMulAction : MulAction Ambient diagram.CosetVertex where
  smul g point := ⟨point.1, g • point.2⟩
  one_smul := by
    rintro ⟨vertex, coset⟩
    change (⟨vertex, (1 : Ambient) • coset⟩ : diagram.CosetVertex) =
      ⟨vertex, coset⟩
    exact congrArg (fun value =>
      (⟨vertex, value⟩ : diagram.CosetVertex)) (one_smul Ambient coset)
  mul_smul first second := by
    rintro ⟨vertex, coset⟩
    change
      (⟨vertex, (first * second) • coset⟩ : diagram.CosetVertex) =
        ⟨vertex, first • second • coset⟩
    exact congrArg (fun value =>
      (⟨vertex, value⟩ : diagram.CosetVertex))
        (mul_smul first second coset)

/-- Left multiplication on coset edges. -/
@[reducible] def cosetEdgeMulAction : MulAction Ambient diagram.CosetEdge where
  smul g point := ⟨point.1, g • point.2⟩
  one_smul := by
    rintro ⟨edge, coset⟩
    change (⟨edge, (1 : Ambient) • coset⟩ : diagram.CosetEdge) =
      ⟨edge, coset⟩
    exact congrArg (fun value =>
      (⟨edge, value⟩ : diagram.CosetEdge)) (one_smul Ambient coset)
  mul_smul first second := by
    rintro ⟨edge, coset⟩
    change
      (⟨edge, (first * second) • coset⟩ : diagram.CosetEdge) =
        ⟨edge, first • second • coset⟩
    exact congrArg (fun value =>
      (⟨edge, value⟩ : diagram.CosetEdge))
        (mul_smul first second coset)

/-- Left multiplication on a lifted edge coset, leaving its base branch
label unchanged. -/
@[reducible] def cosetBranchMulAction :
    MulAction Ambient diagram.cosetSemiGraph.TotalBranch where
  smul g branch :=
    ⟨⟨branch.1.1, g • branch.1.2⟩, branch.2⟩
  one_smul branch := by
    cases branch with
    | mk edge branch =>
        cases edge with
        | mk baseEdge coset =>
            change
              (⟨⟨baseEdge, (1 : Ambient) • coset⟩, branch⟩ :
                  diagram.cosetSemiGraph.TotalBranch) =
                ⟨⟨baseEdge, coset⟩, branch⟩
            congr 2
            simp
  mul_smul first second branch := by
    cases branch with
    | mk edge branch =>
        cases edge with
        | mk baseEdge coset =>
            change
              (⟨⟨baseEdge, (first * second) • coset⟩, branch⟩ :
                  diagram.cosetSemiGraph.TotalBranch) =
                ⟨⟨baseEdge, first • second • coset⟩, branch⟩
            congr 2
            simp [mul_smul]

/-- The ambient group action on the coset semi-graph. -/
def cosetAction : diagram.cosetSemiGraph.Action Ambient where
  vertexAction :=
    @MulAction.toPermHom Ambient diagram.CosetVertex _
      diagram.cosetVertexMulAction
  edgeAction :=
    @MulAction.toPermHom Ambient diagram.CosetEdge _
      diagram.cosetEdgeMulAction
  branchAction :=
    @MulAction.toPermHom Ambient diagram.cosetSemiGraph.TotalBranch _
      diagram.cosetBranchMulAction
  branch_edge := by
    intro g branch
    cases branch with
    | mk edge branch =>
        cases edge with
        | mk baseEdge coset => rfl
  coincidence_action := by
    intro g totalBranch
    rcases totalBranch with ⟨⟨edge, coset⟩, branch⟩
    cases abutment : diagram.base.coincidence edge branch with
    | none =>
        change diagram.cosetSemiGraph.coincidence
            ⟨edge, g • coset⟩ branch =
          (diagram.cosetSemiGraph.coincidence
            ⟨edge, coset⟩ branch).map _
        rw [diagram.cosetSemiGraph_coincidence_of_none abutment]
        rw [diagram.cosetSemiGraph_coincidence_of_none abutment]
        rfl
    | some vertex =>
        change diagram.cosetSemiGraph.coincidence
            ⟨edge, g • coset⟩ branch =
          (diagram.cosetSemiGraph.coincidence
            ⟨edge, coset⟩ branch).map _
        rw [diagram.cosetSemiGraph_coincidence_of_some abutment]
        rw [diagram.cosetSemiGraph_coincidence_of_some abutment]
        change
          some (⟨vertex,
              diagram.branchCosetMap branch abutment (g • coset)⟩ :
                diagram.CosetVertex) =
            some (⟨vertex,
              g • diagram.branchCosetMap branch abutment coset⟩ :
                diagram.CosetVertex)
        rw [diagram.branchCosetMap_smul]

/-- Stabilizer of an arbitrary left coset: a conjugate of the subgroup. -/
theorem stabilizer_leftCoset_eq_conjugate
    (subgroup : Subgroup Ambient) (coset : Ambient ⧸ subgroup) :
    MulAction.stabilizer Ambient coset =
      subgroup.map (MulAut.conj coset.out).toMonoidHom := by
  calc
    MulAction.stabilizer Ambient coset =
        MulAction.stabilizer Ambient
          (coset.out • ((1 : Ambient) : Ambient ⧸ subgroup)) := by
      congr 1
      simp
    _ = (MulAction.stabilizer Ambient
          ((1 : Ambient) : Ambient ⧸ subgroup)).map
            (MulAut.conj coset.out).toMonoidHom :=
      MulAction.stabilizer_smul_eq_stabilizer_map_conj coset.out _
    _ = subgroup.map (MulAut.conj coset.out).toMonoidHom := by
      rw [MulAction.stabilizer_quotient]

/-- The stabilizer of a lifted vertex is the corresponding conjugate
verticial subgroup. -/
theorem cosetAction_vertexStabilizer_eq_conjugate
    (point : diagram.CosetVertex) :
    diagram.cosetAction.vertexStabilizer point =
      (diagram.vertexGroup point.1).map
        (MulAut.conj point.2.out).toMonoidHom := by
  calc
    diagram.cosetAction.vertexStabilizer point =
        MulAction.stabilizer Ambient point.2 := by
      ext g
      change (⟨point.1, g • point.2⟩ : diagram.CosetVertex) = point ↔
        g • point.2 = point.2
      constructor
      · intro equality
        exact eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
      · intro equality
        exact Sigma.ext rfl (heq_of_eq equality)
    _ = (diagram.vertexGroup point.1).map
          (MulAut.conj point.2.out).toMonoidHom :=
      stabilizer_leftCoset_eq_conjugate _ _

/-- The stabilizer of a lifted edge is the corresponding conjugate edge
subgroup. -/
theorem cosetAction_edgeStabilizer_eq_conjugate
    (point : diagram.CosetEdge) :
    diagram.cosetAction.edgeStabilizer point =
      (diagram.edgeGroup point.1).map
        (MulAut.conj point.2.out).toMonoidHom := by
  calc
    diagram.cosetAction.edgeStabilizer point =
        MulAction.stabilizer Ambient point.2 := by
      ext g
      change (⟨point.1, g • point.2⟩ : diagram.CosetEdge) = point ↔
        g • point.2 = point.2
      constructor
      · intro equality
        exact eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
      · intro equality
        exact Sigma.ext rfl (heq_of_eq equality)
    _ = (diagram.edgeGroup point.1).map
          (MulAut.conj point.2.out).toMonoidHom :=
      stabilizer_leftCoset_eq_conjugate _ _

/-- In the coset semi-graph, fixing a lifted edge is equivalent to fixing any
one of its branch labels. -/
theorem cosetAction_branchStabilizer_eq_edgeStabilizer
    (branch : diagram.cosetSemiGraph.TotalBranch) :
    diagram.cosetAction.branchStabilizer branch =
      diagram.cosetAction.edgeStabilizer branch.edge := by
  ext g
  rcases branch with ⟨⟨edge, coset⟩, branch⟩
  change
    (⟨⟨edge, g • coset⟩, branch⟩ :
        diagram.cosetSemiGraph.TotalBranch) =
      ⟨⟨edge, coset⟩, branch⟩ ↔
        (⟨edge, g • coset⟩ : diagram.CosetEdge) = ⟨edge, coset⟩
  constructor
  · intro equality
    have edgeEquality := congrArg
      (fun value : diagram.cosetSemiGraph.TotalBranch => value.edge) equality
    exact edgeEquality
  · intro equality
    have cosetEquality : g • coset = coset :=
      eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
    exact congrArg (fun value =>
      (⟨⟨edge, value⟩, branch⟩ :
        diagram.cosetSemiGraph.TotalBranch)) cosetEquality

end SourceSemiGraphSubgroupDiagram

end Iut
