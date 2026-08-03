/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.GroupTheory.GroupAction.Basic
import Iut.Foundations.SourceSemiGraph

/-!
# Actions and compatible systems of semi-graph components

This module formalizes the group-action content used in *Semi-graphs of
Anabelioids*, Remark 2.2.1.  An action on a raw semi-graph acts coherently on
vertices, edges, and total branches.  A cofiltered finite action system then
acts on its type of compatible sections, and the stabilizer of a section is
proved to be the intersection of its finite-level stabilizers.

The graph-of-groups theorem identifying these stabilizers with the images of
the constituent fundamental groups is not asserted here.
-/

namespace Iut

universe u v w

namespace SourceSemiGraph

variable (G : SourceSemiGraph.{u})

/-- A group action on the raw branch-set data of a semi-graph.  The total
branch action lies over the edge action and carries the coincidence map to the
vertex action. -/
structure Action (Acting : Type v) [Group Acting] where
  vertexAction : Acting →* Equiv.Perm G.Vertex
  edgeAction : Acting →* Equiv.Perm G.Edge
  branchAction : Acting →* Equiv.Perm G.TotalBranch
  branch_edge :
    ∀ g branch,
      (branchAction g branch).edge = edgeAction g branch.edge
  coincidence_action :
    ∀ g branch,
      G.coincidenceTotal (branchAction g branch) =
        (G.coincidenceTotal branch).map (vertexAction g)

namespace Action

variable {G : SourceSemiGraph.{u}} {Acting : Type v} [Group Acting]
    (data : G.Action Acting)

/-- The vertex permutation gives the corresponding multiplicative action. -/
@[reducible] def vertexMulAction : MulAction Acting G.Vertex where
  smul g vertex := data.vertexAction g vertex
  one_smul vertex := by
    change data.vertexAction 1 vertex = vertex
    rw [map_one]
    rfl
  mul_smul first second vertex := by
    change data.vertexAction (first * second) vertex =
      data.vertexAction first (data.vertexAction second vertex)
    rw [map_mul]
    exact Equiv.Perm.mul_apply _ _ _

/-- The edge permutation gives the corresponding multiplicative action. -/
@[reducible] def edgeMulAction : MulAction Acting G.Edge where
  smul g edge := data.edgeAction g edge
  one_smul edge := by
    change data.edgeAction 1 edge = edge
    rw [map_one]
    rfl
  mul_smul first second edge := by
    change data.edgeAction (first * second) edge =
      data.edgeAction first (data.edgeAction second edge)
    rw [map_mul]
    exact Equiv.Perm.mul_apply _ _ _

/-- The total-branch permutation gives the corresponding multiplicative
action. -/
@[reducible] def branchMulAction : MulAction Acting G.TotalBranch where
  smul g branch := data.branchAction g branch
  one_smul branch := by
    change data.branchAction 1 branch = branch
    rw [map_one]
    rfl
  mul_smul first second branch := by
    change data.branchAction (first * second) branch =
      data.branchAction first (data.branchAction second branch)
    rw [map_mul]
    exact Equiv.Perm.mul_apply _ _ _

/-- The subgroup fixing a raw vertex. -/
def vertexStabilizer (vertex : G.Vertex) : Subgroup Acting :=
  @MulAction.stabilizer Acting G.Vertex _ data.vertexMulAction vertex

/-- The subgroup fixing a raw edge. -/
def edgeStabilizer (edge : G.Edge) : Subgroup Acting :=
  @MulAction.stabilizer Acting G.Edge _ data.edgeMulAction edge

/-- The subgroup fixing a total branch. -/
def branchStabilizer (branch : G.TotalBranch) : Subgroup Acting :=
  @MulAction.stabilizer Acting G.TotalBranch _ data.branchMulAction branch

@[simp]
theorem mem_vertexStabilizer_iff {vertex : G.Vertex} {g : Acting} :
    g ∈ data.vertexStabilizer vertex ↔
      data.vertexAction g vertex = vertex := by
  rfl

@[simp]
theorem mem_edgeStabilizer_iff {edge : G.Edge} {g : Acting} :
    g ∈ data.edgeStabilizer edge ↔ data.edgeAction g edge = edge := by
  rfl

@[simp]
theorem mem_branchStabilizer_iff {branch : G.TotalBranch} {g : Acting} :
    g ∈ data.branchStabilizer branch ↔
      data.branchAction g branch = branch := by
  rfl

/-- A group element fixing a branch fixes its supporting edge. -/
theorem branchStabilizer_le_edgeStabilizer (branch : G.TotalBranch) :
    data.branchStabilizer branch ≤ data.edgeStabilizer branch.edge := by
  intro g branch_fixed
  rw [data.mem_edgeStabilizer_iff]
  have edge_image := data.branch_edge g branch
  rw [data.mem_branchStabilizer_iff] at branch_fixed
  calc
    data.edgeAction g branch.edge =
        (data.branchAction g branch).edge := edge_image.symm
    _ = branch.edge :=
      congrArg (fun value : G.TotalBranch => value.edge) branch_fixed

/-- A group element fixing a branch that abuts a vertex also fixes that
vertex. -/
theorem branchStabilizer_le_vertexStabilizer
    {branch : G.TotalBranch} {vertex : G.Vertex}
    (abuts : G.coincidenceTotal branch = some vertex) :
    data.branchStabilizer branch ≤ data.vertexStabilizer vertex := by
  intro g branch_fixed
  rw [data.mem_vertexStabilizer_iff]
  rw [data.mem_branchStabilizer_iff] at branch_fixed
  have coincidence_image := data.coincidence_action g branch
  rw [branch_fixed, abuts] at coincidence_image
  exact Option.some.inj coincidence_image.symm

/-- The action maps an incident branch at a vertex to an incident branch at
the image vertex. -/
def actIncidentBranch (g : Acting) (vertex : G.Vertex) :
    G.IncidentBranch vertex →
      G.IncidentBranch (data.vertexAction g vertex)
  | ⟨branch, abuts⟩ =>
      ⟨data.branchAction g branch, by
        rw [data.coincidence_action, abuts]
        rfl⟩

/-- The induced action map on incident branches is injective. -/
theorem actIncidentBranch_injective (g : Acting) (vertex : G.Vertex) :
    Function.Injective (data.actIncidentBranch g vertex) := by
  intro first second equality
  apply Subtype.ext
  exact (data.branchAction g).injective
    (congrArg Subtype.val equality)

/-- The induced action map on incident branches is surjective. -/
theorem actIncidentBranch_surjective (g : Acting) (vertex : G.Vertex) :
    Function.Surjective (data.actIncidentBranch g vertex) := by
  intro target
  let sourceBranch := data.branchAction g⁻¹ target.1
  have source_abuts :
      G.coincidenceTotal sourceBranch = some vertex := by
    rw [data.coincidence_action]
    rw [target.2]
    simp [map_inv]
  refine ⟨⟨sourceBranch, source_abuts⟩, ?_⟩
  apply Subtype.ext
  change data.branchAction g sourceBranch = target.1
  simp [sourceBranch, map_inv]

/-- Every raw semi-graph action is locally bijective on incident branches. -/
theorem actIncidentBranch_bijective (g : Acting) (vertex : G.Vertex) :
    Function.Bijective (data.actIncidentBranch g vertex) :=
  ⟨data.actIncidentBranch_injective g vertex,
    data.actIncidentBranch_surjective g vertex⟩

end Action

end SourceSemiGraph

open CategoryTheory CategoryTheory.FunctorToTypes

/-- A cofiltered inverse system of finite group-sets with equivariant
transition maps.  Its sections are the compatible systems occurring in
Remark 2.2.1. -/
structure SourceCofilteredFiniteActionSystem
    (Index : Type u) [Category.{w} Index] [IsCofilteredOrEmpty Index]
    (Acting : Type v) [Group Acting] where
  carrier : Index ⥤ Type v
  action : ∀ index, Acting →* Equiv.Perm (carrier.obj index)
  transition_equivariant :
    ∀ {source target} (map : source ⟶ target) g value,
      carrier.map map (action source g value) =
        action target g (carrier.map map value)
  finite_level : ∀ index, Finite (carrier.obj index)

namespace SourceCofilteredFiniteActionSystem

variable
  {Index : Type u} [Category.{w} Index] [IsCofilteredOrEmpty Index]
  {Acting : Type v} [Group Acting]
  (system : SourceCofilteredFiniteActionSystem Index Acting)

/-- Act componentwise on a compatible section. -/
def actSection (g : Acting) (compatible : system.carrier.sections) :
    system.carrier.sections :=
  ⟨fun index => system.action index g (compatible.1 index), by
    intro source target map
    rw [system.transition_equivariant map]
    rw [compatible.property map]⟩

@[simp]
theorem actSection_apply (g : Acting)
    (compatible : system.carrier.sections) (index : Index) :
    (system.actSection g compatible).1 index =
      system.action index g (compatible.1 index) :=
  rfl

/-- The componentwise action is a permutation of compatible sections. -/
def sectionPerm (g : Acting) : Equiv.Perm system.carrier.sections where
  toFun := system.actSection g
  invFun := system.actSection g⁻¹
  left_inv := by
    intro compatible
    apply CategoryTheory.Functor.sections_ext_iff.mpr
    intro index
    simp [actSection, map_inv]
  right_inv := by
    intro compatible
    apply CategoryTheory.Functor.sections_ext_iff.mpr
    intro index
    simp [actSection, map_inv]

/-- The acting group acts on the inverse limit of compatible sections. -/
def sectionAction : Acting →* Equiv.Perm system.carrier.sections where
  toFun := system.sectionPerm
  map_one' := by
    apply Equiv.ext
    intro compatible
    apply CategoryTheory.Functor.sections_ext_iff.mpr
    intro index
    simp [sectionPerm, actSection]
  map_mul' := by
    intro first second
    apply Equiv.ext
    intro compatible
    apply CategoryTheory.Functor.sections_ext_iff.mpr
    intro index
    simp [sectionPerm, actSection, map_mul, Equiv.Perm.mul_apply]

/-- The multiplicative action on compatible sections. -/
@[reducible] def sectionMulAction : MulAction Acting system.carrier.sections where
  smul g compatible := system.sectionAction g compatible
  one_smul compatible := by
    change system.sectionAction 1 compatible = compatible
    rw [map_one]
    rfl
  mul_smul first second compatible := by
    change system.sectionAction (first * second) compatible =
      system.sectionAction first (system.sectionAction second compatible)
    rw [map_mul]
    exact Equiv.Perm.mul_apply _ _ _

/-- The stabilizer of a compatible system. -/
def sectionStabilizer (compatible : system.carrier.sections) : Subgroup Acting :=
  @MulAction.stabilizer Acting system.carrier.sections _
    system.sectionMulAction compatible

/-- The stabilizer of one finite-level coordinate of a compatible system. -/
def coordinateStabilizer (compatible : system.carrier.sections) (index : Index) :
    Subgroup Acting :=
  { carrier := {g |
      system.action index g (compatible.1 index) = compatible.1 index}
    one_mem' := by simp
    mul_mem' := by
      intro first second first_mem second_mem
      change system.action index first (compatible.1 index) =
        compatible.1 index at first_mem
      change system.action index second (compatible.1 index) =
        compatible.1 index at second_mem
      change system.action index (first * second) (compatible.1 index) =
        compatible.1 index
      rw [map_mul, Equiv.Perm.mul_apply, second_mem, first_mem]
    inv_mem' := by
      intro g g_mem
      change system.action index g (compatible.1 index) =
        compatible.1 index at g_mem
      change system.action index g⁻¹ (compatible.1 index) =
        compatible.1 index
      apply (system.action index g).injective
      simp [map_inv, g_mem] }

@[simp]
theorem mem_sectionStabilizer_iff
    {compatible : system.carrier.sections} {g : Acting} :
    g ∈ system.sectionStabilizer compatible ↔
      system.actSection g compatible = compatible := by
  rfl

@[simp]
theorem mem_coordinateStabilizer_iff
    {compatible : system.carrier.sections} {index : Index} {g : Acting} :
    g ∈ system.coordinateStabilizer compatible index ↔
      system.action index g (compatible.1 index) = compatible.1 index := by
  rfl

/-- An element fixes a compatible system exactly when it fixes every
finite-level coordinate. -/
theorem mem_sectionStabilizer_iff_forall_coordinate
    {compatible : system.carrier.sections} {g : Acting} :
    g ∈ system.sectionStabilizer compatible ↔
      ∀ index, g ∈ system.coordinateStabilizer compatible index := by
  rw [system.mem_sectionStabilizer_iff]
  constructor
  · intro section_fixed index
    rw [system.mem_coordinateStabilizer_iff]
    exact congrArg (fun value => value.1 index) section_fixed
  · intro coordinate_fixed
    apply CategoryTheory.Functor.sections_ext_iff.mpr
    intro index
    exact coordinate_fixed index

/-- The stabilizer of a compatible system is the intersection of all of its
finite-level stabilizers. -/
theorem sectionStabilizer_eq_iInf_coordinateStabilizer
    (compatible : system.carrier.sections) :
    system.sectionStabilizer compatible =
      ⨅ index, system.coordinateStabilizer compatible index := by
  ext g
  rw [system.mem_sectionStabilizer_iff_forall_coordinate]
  simp

end SourceCofilteredFiniteActionSystem

end Iut
