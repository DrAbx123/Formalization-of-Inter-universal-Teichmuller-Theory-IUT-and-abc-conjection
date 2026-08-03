/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homeomorph.Defs

/-!
# Source-faithful Aut-holomorphic assignments

Absolute Anabelian Topics III, Definition 2.1 assigns to every connected open
subset `U` of a Riemann surface the group `Aut_hol(U)`.  This file constructs
that assignment for connected open subsets of the complex plane.  An element
is an actual homeomorphism of `U` for which both directions admit ambient
complex-differentiable lifts on `U`; the group structure is derived from
composition and inversion.
-/

open Set

namespace Iut

noncomputable section

namespace SourceAutHolomorphic

/-- A nonempty connected open subset of the complex plane. -/
structure ConnectedOpen where
  carrier : Set ℂ
  isOpen_carrier : IsOpen carrier
  isConnected_carrier : IsConnected carrier

namespace ConnectedOpen

theorem nonempty (U : ConnectedOpen) : U.carrier.Nonempty :=
  U.isConnected_carrier.nonempty

theorem isPreconnected (U : ConnectedOpen) :
    IsPreconnected U.carrier :=
  U.isConnected_carrier.isPreconnected

end ConnectedOpen

/--
A map between complex open subspaces is holomorphic when its values are the
restriction of an ambient map that is complex differentiable on the source.
Because the source is open, this is the usual local holomorphicity condition;
the ambient map carries no data in the definition.
-/
def HasAmbientHolomorphicLift
    (U V : ConnectedOpen) (map : U.carrier → V.carrier) : Prop :=
  ∃ ambient : ℂ → ℂ,
    DifferentiableOn ℂ ambient U.carrier ∧
      ∀ value : U.carrier, ambient value = map value

namespace HasAmbientHolomorphicLift

theorem id (U : ConnectedOpen) :
    HasAmbientHolomorphicLift U U _root_.id := by
  refine ⟨_root_.id, differentiable_id.differentiableOn, ?_⟩
  intro value
  rfl

theorem comp
    {U V W : ConnectedOpen}
    {first : U.carrier → V.carrier}
    {second : V.carrier → W.carrier}
    (hfirst : HasAmbientHolomorphicLift U V first)
    (hsecond : HasAmbientHolomorphicLift V W second) :
    HasAmbientHolomorphicLift U W (second ∘ first) := by
  obtain ⟨firstAmbient, hfirstDifferentiable, hfirstEq⟩ := hfirst
  obtain ⟨secondAmbient, hsecondDifferentiable, hsecondEq⟩ := hsecond
  refine ⟨secondAmbient ∘ firstAmbient, ?_, ?_⟩
  · exact hsecondDifferentiable.comp hfirstDifferentiable fun value hvalue ↦ by
      rw [hfirstEq ⟨value, hvalue⟩]
      exact (first ⟨value, hvalue⟩).2
  · intro value
    change secondAmbient (firstAmbient value) = second (first value)
    rw [hfirstEq value]
    exact hsecondEq (first value)

end HasAmbientHolomorphicLift

/-- The actual group `Aut_hol(U)` assigned to a connected complex open `U`. -/
def autHolomorphicSubgroup (U : ConnectedOpen) :
    Subgroup (U.carrier ≃ₜ U.carrier) where
  carrier automorphism :=
    HasAmbientHolomorphicLift U U automorphism ∧
      HasAmbientHolomorphicLift U U automorphism.symm
  one_mem' := by
    exact ⟨HasAmbientHolomorphicLift.id U, HasAmbientHolomorphicLift.id U⟩
  mul_mem' := by
    intro first second hfirst hsecond
    constructor
    · simpa only [Homeomorph.mul_apply] using
        HasAmbientHolomorphicLift.comp hsecond.1 hfirst.1
    · change HasAmbientHolomorphicLift U U
        ((first * second : U.carrier ≃ₜ U.carrier).symm)
      simpa only [mul_inv_rev, Homeomorph.mul_apply, Homeomorph.inv_apply] using
        HasAmbientHolomorphicLift.comp hfirst.2 hsecond.2
  inv_mem' := by
    intro automorphism hautomorphism
    exact ⟨hautomorphism.2, by simpa using hautomorphism.1⟩

/-- The source assignment `U ↦ Aut_hol(U)`. -/
abbrev AutHolomorphic (U : ConnectedOpen) :=
  autHolomorphicSubgroup U

namespace AutHolomorphic

variable {U V W : ConnectedOpen}

theorem holomorphic (automorphism : AutHolomorphic U) :
    HasAmbientHolomorphicLift U U automorphism :=
  by
    have hautomorphism := automorphism.property
    change HasAmbientHolomorphicLift U U automorphism.1 ∧
      HasAmbientHolomorphicLift U U automorphism.1.symm at hautomorphism
    exact hautomorphism.1

theorem holomorphic_symm (automorphism : AutHolomorphic U) :
    HasAmbientHolomorphicLift U U automorphism.1.symm :=
  by
    have hautomorphism := automorphism.property
    change HasAmbientHolomorphicLift U U automorphism.1 ∧
      HasAmbientHolomorphicLift U U automorphism.1.symm at hautomorphism
    exact hautomorphism.2

/-- The identity member of the assigned automorphism group. -/
def identity (U : ConnectedOpen) : AutHolomorphic U :=
  1

@[simp]
theorem identity_apply (U : ConnectedOpen) (value : U.carrier) :
    (identity U).1 value = value :=
  rfl

@[simp]
theorem multiplication_apply
    (first second : AutHolomorphic U) (value : U.carrier) :
    (first * second).1 value = first.1 (second.1 value) := by
  exact Homeomorph.mul_apply first.1 second.1 value

@[simp]
theorem inverse_apply_apply
    (automorphism : AutHolomorphic U) (value : U.carrier) :
    (automorphism⁻¹).1 (automorphism.1 value) = value := by
  exact automorphism.1.symm_apply_apply value

@[simp]
theorem apply_inverse_apply
    (automorphism : AutHolomorphic U) (value : U.carrier) :
    automorphism.1 ((automorphism⁻¹).1 value) = value := by
  exact automorphism.1.apply_symm_apply value

/-- A connected open subobject used to state restriction of automorphisms. -/
structure RestrictionDomain (U : ConnectedOpen) where
  openSubset : ConnectedOpen
  inclusion : openSubset.carrier ⊆ U.carrier

/-- An automorphism preserves a connected open restriction domain in both directions. -/
def Preserves
    (domain : RestrictionDomain U)
    (automorphism : AutHolomorphic U) : Prop :=
  (∀ value : domain.openSubset.carrier,
      (automorphism.1 ⟨value, domain.inclusion value.2⟩ : ℂ) ∈
        domain.openSubset.carrier) ∧
    (∀ value : domain.openSubset.carrier,
      ((automorphism⁻¹).1 ⟨value, domain.inclusion value.2⟩ : ℂ) ∈
        domain.openSubset.carrier)

/-- Restriction of a preserving `Aut_hol(U)` element to `Aut_hol(V)`. -/
def restrict
    (domain : RestrictionDomain U)
    (automorphism : AutHolomorphic U)
    (hpreserves : Preserves domain automorphism) :
    AutHolomorphic domain.openSubset := by
  let restricted : domain.openSubset.carrier ≃ₜ domain.openSubset.carrier :=
    { toFun := fun value ↦
        ⟨automorphism.1 ⟨value, domain.inclusion value.2⟩,
          hpreserves.1 value⟩
      invFun := fun value ↦
        ⟨(automorphism⁻¹).1 ⟨value, domain.inclusion value.2⟩,
          hpreserves.2 value⟩
      left_inv := fun value ↦ by
        apply Subtype.ext
        change
          (((automorphism.1).symm
            (automorphism.1 ⟨value, domain.inclusion value.2⟩) : U.carrier) : ℂ) =
              value
        exact congrArg Subtype.val <|
          automorphism.1.symm_apply_apply
            ⟨value, domain.inclusion value.2⟩
      right_inv := fun value ↦ by
        apply Subtype.ext
        change
          ((automorphism.1
            (automorphism.1.symm ⟨value, domain.inclusion value.2⟩) : U.carrier) : ℂ) =
              value
        exact congrArg Subtype.val <|
          automorphism.1.apply_symm_apply
            ⟨value, domain.inclusion value.2⟩
      continuous_toFun := by
        have hinclusion : Continuous
            (fun value : domain.openSubset.carrier ↦
              (⟨value, domain.inclusion value.2⟩ : U.carrier)) :=
          continuous_subtype_val.subtype_mk _
        have hambient : Continuous
            (fun value : domain.openSubset.carrier ↦
              (automorphism.1 ⟨value, domain.inclusion value.2⟩ : ℂ)) := by
          simpa only [Function.comp_apply] using
            continuous_subtype_val.comp
              (automorphism.1.continuous.comp hinclusion)
        exact hambient.subtype_mk _
      continuous_invFun := by
        have hinclusion : Continuous
            (fun value : domain.openSubset.carrier ↦
              (⟨value, domain.inclusion value.2⟩ : U.carrier)) :=
          continuous_subtype_val.subtype_mk _
        have hambient : Continuous
            (fun value : domain.openSubset.carrier ↦
              (automorphism.1.symm
                ⟨value, domain.inclusion value.2⟩ : ℂ)) := by
          simpa only [Function.comp_apply] using
            continuous_subtype_val.comp
              (automorphism.1.symm.continuous.comp hinclusion)
        simpa only [Subgroup.coe_inv, Homeomorph.inv_apply] using
          hambient.subtype_mk _ }
  refine ⟨restricted, ?_⟩
  change HasAmbientHolomorphicLift domain.openSubset domain.openSubset restricted ∧
    HasAmbientHolomorphicLift domain.openSubset domain.openSubset restricted.symm
  constructor
  · obtain ⟨ambient, hambient, heq⟩ := holomorphic automorphism
    refine ⟨ambient, hambient.mono domain.inclusion, ?_⟩
    intro value
    simpa only using heq ⟨value, domain.inclusion value.2⟩
  · obtain ⟨ambient, hambient, heq⟩ := holomorphic_symm automorphism
    refine ⟨ambient, hambient.mono domain.inclusion, ?_⟩
    intro value
    simpa only [Subgroup.coe_inv, Homeomorph.inv_apply] using
      heq ⟨value, domain.inclusion value.2⟩

@[simp]
theorem restrict_apply
    (domain : RestrictionDomain U)
    (automorphism : AutHolomorphic U)
    (hpreserves : Preserves domain automorphism)
    (value : domain.openSubset.carrier) :
    ((restrict domain automorphism hpreserves).1 value : ℂ) =
      automorphism.1 ⟨value, domain.inclusion value.2⟩ :=
  rfl

theorem identity_preserves (domain : RestrictionDomain U) :
    Preserves domain (identity U) := by
  constructor <;> intro value <;> exact value.2

@[simp]
theorem restrict_identity (domain : RestrictionDomain U) :
    restrict domain (identity U) (identity_preserves domain) =
      identity domain.openSubset := by
  apply Subtype.ext
  ext value
  rfl

theorem mul_preserves
    (domain : RestrictionDomain U)
    (first second : AutHolomorphic U)
    (hfirst : Preserves domain first)
    (hsecond : Preserves domain second) :
    Preserves domain (first * second) := by
  constructor
  · intro value
    change
      ((first.1 * second.1)
        ⟨value, domain.inclusion value.2⟩ : ℂ) ∈
          domain.openSubset.carrier
    rw [Homeomorph.mul_apply]
    exact hfirst.1 ⟨second.1 ⟨value, domain.inclusion value.2⟩,
      hsecond.1 value⟩
  · intro value
    change
      ((first.1 * second.1)⁻¹
        ⟨value, domain.inclusion value.2⟩ : ℂ) ∈
          domain.openSubset.carrier
    rw [mul_inv_rev, Homeomorph.mul_apply, Homeomorph.inv_apply]
    exact hsecond.2 ⟨(first⁻¹).1 ⟨value, domain.inclusion value.2⟩,
      hfirst.2 value⟩

theorem inv_preserves
    (domain : RestrictionDomain U)
    (automorphism : AutHolomorphic U)
    (hpreserves : Preserves domain automorphism) :
    Preserves domain automorphism⁻¹ := by
  constructor
  · intro value
    exact hpreserves.2 value
  · intro value
    simpa using hpreserves.1 value

@[simp]
theorem restrict_mul
    (domain : RestrictionDomain U)
    (first second : AutHolomorphic U)
    (hfirst : Preserves domain first)
    (hsecond : Preserves domain second) :
    restrict domain (first * second)
        (mul_preserves domain first second hfirst hsecond) =
      restrict domain first hfirst * restrict domain second hsecond := by
  apply Subtype.ext
  ext value
  rfl

@[simp]
theorem restrict_inv
    (domain : RestrictionDomain U)
    (automorphism : AutHolomorphic U)
    (hpreserves : Preserves domain automorphism) :
    restrict domain automorphism⁻¹
        (inv_preserves domain automorphism hpreserves) =
      (restrict domain automorphism hpreserves)⁻¹ := by
  apply Subtype.ext
  ext value
  rfl

end AutHolomorphic

end SourceAutHolomorphic

end

end Iut
