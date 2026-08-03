/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceSemiGraph

/-!
# Finite-sheet covers from branch permutations

A permutation of a fixed sheet over every total branch of a semi-graph gives
a finite-sheet graph cover.  The edge sheet is transported by the branch
permutation when that branch abuts a vertex.  This is the voltage-cover
constructor used in the residual-finiteness step of *Semi-graphs of
Anabelioids*, Corollary 1.7.
-/

namespace Iut

universe u

namespace SourceFiniteSheetSemiGraphCover

variable (base : SourceSemiGraph.{u}) (Sheet : Type u)
    (transport : ∀ edge : base.Edge, base.Branch edge → Equiv.Perm Sheet)

/-- The finite-sheet semi-graph determined by branch transports. -/
def cover : SourceSemiGraph.{u} where
  Vertex := base.Vertex × Sheet
  Edge := base.Edge × Sheet
  Branch edge := base.Branch edge.1
  branchFintype edge := base.branchFintype edge.1
  branch_card edge := base.branch_card edge.1
  coincidence edge branch :=
    (base.coincidence edge.1 branch).map fun vertex =>
      (vertex, transport edge.1 branch edge.2)

/-- Forget the sheet coordinate. -/
def projection : (cover base Sheet transport).Hom base where
  vertexMap := Prod.fst
  edgeMap := Prod.fst
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro edge branch vertex coincidence
    change Option.map _ (base.coincidence edge.1 branch) = some vertex at coincidence
    rcases edge with ⟨edge, sheet⟩
    rcases vertex with ⟨vertex, vertexSheet⟩
    simp only [Option.map_eq_some_iff] at coincidence
    obtain ⟨target, targetCoincidence, equality⟩ := coincidence
    cases equality
    exact targetCoincidence

@[simp]
theorem projection_vertexMap (vertex : (cover base Sheet transport).Vertex) :
    (projection base Sheet transport).vertexMap vertex = vertex.1 :=
  rfl

@[simp]
theorem projection_edgeMap (edge : (cover base Sheet transport).Edge) :
    (projection base Sheet transport).edgeMap edge = edge.1 :=
  rfl

@[simp]
theorem projection_branchEquiv
    (edge : (cover base Sheet transport).Edge)
    (branch : (cover base Sheet transport).Branch edge) :
    (projection base Sheet transport).branchEquiv edge branch = branch :=
  rfl

theorem projection_isProper :
    (projection base Sheet transport).IsProper := by
  intro edge branch
  rcases edge with ⟨edge, sheet⟩
  change
    (∃ vertex, Option.map (fun target =>
        (target, transport edge branch sheet))
        (base.coincidence edge branch) = some vertex) ↔
      ∃ vertex, base.coincidence edge branch = some vertex
  constructor
  · rintro ⟨⟨vertex, vertexSheet⟩, coincidence⟩
    simp only [Option.map_eq_some_iff] at coincidence
    obtain ⟨target, targetCoincidence, _⟩ := coincidence
    exact ⟨target, targetCoincidence⟩
  · rintro ⟨vertex, coincidence⟩
    exact ⟨(vertex, transport edge branch sheet), by simp [coincidence]⟩

/-- The unique lift of an incident branch at a selected vertex sheet. -/
noncomputable def liftIncidentBranch (vertex : base.Vertex × Sheet) :
    base.IncidentBranch vertex.1 →
      (cover base Sheet transport).IncidentBranch vertex
  | ⟨⟨edge, branch⟩, coincidence⟩ =>
      ⟨⟨⟨edge, (transport edge branch)⁻¹ vertex.2⟩, branch⟩, by
        change base.coincidence edge branch = some vertex.1 at coincidence
        change Option.map (fun target =>
            (target, transport edge branch
              ((transport edge branch)⁻¹ vertex.2)))
            (base.coincidence edge branch) = some vertex
        rw [coincidence]
        simp⟩

@[simp]
theorem incidentBranchMap_liftIncidentBranch
    (vertex : base.Vertex × Sheet)
    (branch : base.IncidentBranch vertex.1) :
    (projection base Sheet transport).incidentBranchMap vertex
        (liftIncidentBranch base Sheet transport vertex branch) = branch := by
  rcases branch with ⟨⟨edge, branch⟩, coincidence⟩
  rfl

@[simp]
theorem liftIncidentBranch_incidentBranchMap
    (vertex : base.Vertex × Sheet)
    (branch : (cover base Sheet transport).IncidentBranch vertex) :
    liftIncidentBranch base Sheet transport vertex
        ((projection base Sheet transport).incidentBranchMap vertex branch) =
      branch := by
  rcases branch with ⟨⟨⟨edge, sheet⟩, branch⟩, coincidence⟩
  apply Subtype.ext
  apply Sigma.ext
  · apply Prod.ext
    · rfl
    · change (transport edge branch)⁻¹ vertex.2 = sheet
      change Option.map (fun target =>
          (target, transport edge branch sheet))
          (base.coincidence edge branch) = some vertex at coincidence
      simp only [Option.map_eq_some_iff] at coincidence
      obtain ⟨target, targetCoincidence, equality⟩ := coincidence
      have sheetEquality : transport edge branch sheet = vertex.2 :=
        congrArg Prod.snd equality
      apply (transport edge branch).injective
      simpa using sheetEquality.symm
  · rfl

theorem projection_incidentBranch_bijective
    (vertex : (cover base Sheet transport).Vertex) :
    Function.Bijective
      ((projection base Sheet transport).incidentBranchMap vertex) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨liftIncidentBranch base Sheet transport vertex,
      liftIncidentBranch_incidentBranchMap base Sheet transport vertex,
      incidentBranchMap_liftIncidentBranch base Sheet transport vertex⟩

/-- Branch permutations always define a graph covering. -/
theorem projection_isGraphCovering :
    (projection base Sheet transport).IsGraphCovering :=
  ⟨projection_isProper base Sheet transport,
    projection_incidentBranch_bijective base Sheet transport⟩

instance cover_vertex_finite [Finite base.Vertex] [Finite Sheet] :
    Finite (cover base Sheet transport).Vertex := by
  change Finite (base.Vertex × Sheet)
  infer_instance

instance cover_edge_finite [Finite base.Edge] [Finite Sheet] :
    Finite (cover base Sheet transport).Edge := by
  change Finite (base.Edge × Sheet)
  infer_instance

end SourceFiniteSheetSemiGraphCover

end Iut
