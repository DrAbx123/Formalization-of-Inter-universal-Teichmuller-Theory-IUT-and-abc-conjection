/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors

Extracted from promachina/iut-lean@581e2b898b8429cbb696f75c4548e732d440650d.
The carrier was generalized from TopologicalGroupCat to an arbitrary
topological group; the source-specific topological-group wrapper was omitted.
-/
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Nested normal quotient systems

A decreasing sequence of normal subgroups defines a tower of quotient groups.
This module constructs its transition maps and compatible-family limit, then
proves that the canonical map into the limit is injective when the kernels
have trivial intersection.
-/

namespace Iut

universe u
/-- A nested normal-kernel certificate.  The quotient levels and transition
maps are definitions, not fields. -/
structure SourceNestedNormalQuotientSystem
    (group : Type u) [Group group] [TopologicalSpace group]
    [IsTopologicalGroup group] where
  kernel : ℕ → Subgroup group
  normal : ∀ level, (kernel level).Normal
  antitone : Antitone kernel

namespace SourceNestedNormalQuotientSystem

variable {group : Type u} [Group group] [TopologicalSpace group]
  [IsTopologicalGroup group]
variable (system : SourceNestedNormalQuotientSystem group)

instance kernelNormal (level : ℕ) : (system.kernel level).Normal :=
  system.normal level

/-- The actual quotient group at one outer-extension level. -/
abbrev Level (level : ℕ) := group ⧸ system.kernel level

/-- The canonical quotient transition from a finer to a coarser level. -/
def transition {coarser finer : ℕ} (refines : coarser ≤ finer) :
    system.Level finer →* system.Level coarser :=
  QuotientGroup.map
    (system.kernel finer) (system.kernel coarser)
    (MonoidHom.id group) (system.antitone refines)

@[simp]
theorem transition_mk {coarser finer : ℕ} (refines : coarser ≤ finer)
    (value : group) :
    system.transition refines
        (QuotientGroup.mk' (system.kernel finer) value) =
      QuotientGroup.mk' (system.kernel coarser) value :=
  rfl

theorem transition_surjective {coarser finer : ℕ}
    (refines : coarser ≤ finer) :
    Function.Surjective (system.transition refines) := by
  intro target
  induction target using Quotient.inductionOn' with
  | _ value =>
      exact ⟨QuotientGroup.mk' (system.kernel finer) value, rfl⟩

/-- Quotient transitions are continuous for the canonical quotient
topologies. -/
theorem transition_continuous {coarser finer : ℕ}
    (refines : coarser ≤ finer) :
    Continuous (system.transition refines) := by
  apply (QuotientGroup.isQuotientMap_mk
    (system.kernel finer)).continuous_iff.mpr
  change Continuous (fun value : group =>
    system.transition refines
      (QuotientGroup.mk' (system.kernel finer) value))
  rw [show (fun value : group =>
      system.transition refines
        (QuotientGroup.mk' (system.kernel finer) value)) =
      (QuotientGroup.mk : group -> system.Level coarser) by
    funext value
    exact system.transition_mk refines value]
  exact QuotientGroup.continuous_mk

/-- Compatible coordinates in the quotient tower. -/
def Compatible (coordinates : ∀ level, system.Level level) : Prop :=
  ∀ {coarser finer}, (refines : coarser ≤ finer) →
    system.transition refines (coordinates finer) = coordinates coarser

/-- Compatible families form the literal inverse-limit subgroup of the
product of all quotient levels. -/
def compatibleSubgroup : Subgroup (∀ level, system.Level level) where
  carrier := {coordinates | system.Compatible coordinates}
  one_mem' := by
    intro coarser finer refines
    exact map_one (system.transition refines)
  mul_mem' := by
    intro first second firstCompatible secondCompatible coarser finer refines
    simp only [Pi.mul_apply, map_mul]
    rw [firstCompatible refines, secondCompatible refines]
  inv_mem' := by
    intro coordinates compatible coarser finer refines
    simp only [Pi.inv_apply, map_inv]
    rw [compatible refines]

/-- The literal compatible-family inverse limit. -/
abbrev Limit := system.compatibleSubgroup

/-- A coordinate projection of the literal limit. -/
def projection (level : ℕ) : system.Limit →* system.Level level where
  toFun coordinates := coordinates.1 level
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical map from the fixed arithmetic group into its quotient
inverse limit. -/
def canonicalMap : group →* system.Limit where
  toFun value :=
    ⟨fun level => QuotientGroup.mk' (system.kernel level) value, by
      intro coarser finer refines
      exact system.transition_mk refines value⟩
  map_one' := by ext level; rfl
  map_mul' first second := by ext level; rfl

/-- The canonical map to compatible quotient coordinates is continuous. -/
theorem canonicalMap_continuous : Continuous system.canonicalMap := by
  exact (continuous_pi fun _ => QuotientGroup.continuous_mk).subtype_mk _

theorem canonicalMap_projection (level : ℕ) (value : group) :
    system.projection level (system.canonicalMap value) =
      QuotientGroup.mk' (system.kernel level) value :=
  rfl

/-- The canonical map is injective when the specialization kernels have
trivial intersection. -/
theorem canonicalMap_injective
    (exhaustive : (⨅ level, system.kernel level) = ⊥) :
    Function.Injective system.canonicalMap := by
  intro first second equality
  apply mul_inv_eq_one.mp
  have membership : first / second ∈ ⨅ level, system.kernel level := by
    rw [Subgroup.mem_iInf]
    intro level
    have coordinateEquality := congrArg
      (fun compatible : system.Limit => compatible.1 level) equality
    change QuotientGroup.mk' (system.kernel level) first =
      QuotientGroup.mk' (system.kernel level) second at coordinateEquality
    exact QuotientGroup.eq_iff_div_mem.mp coordinateEquality
  rw [exhaustive] at membership
  have quotientTrivial : first / second = 1 := by
    simpa only [Subgroup.mem_bot] using membership
  simpa only [div_eq_mul_inv] using quotientTrivial

end SourceNestedNormalQuotientSystem
end Iut
