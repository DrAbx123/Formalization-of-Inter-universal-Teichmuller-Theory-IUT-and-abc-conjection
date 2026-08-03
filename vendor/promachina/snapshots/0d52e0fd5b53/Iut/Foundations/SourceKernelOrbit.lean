/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceAnabelioidSlice
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Kernel orbits of continuous actions

This file contains the carrier-level construction shared by finite covering
categories and countable temperoids.  Given a continuous surjection `Pi → G`,
it equips the `ker(q)`-orbits of any discrete continuous `Pi`-action with the
descended continuous `G`-action.

Continuity is proved pointwise: the image of the open stabilizer of a chosen
representative fixes its orbit class.  This proof applies equally to finite and
countable carriers and deliberately does not use a finite global kernel.
-/

namespace Iut

universe u

open CategoryTheory

namespace SourceKernelOrbit

variable {Pi G : Type u}
variable [Group Pi] [TopologicalSpace Pi]
variable [Group G] [TopologicalSpace G]
variable (q : Pi →ₜ* G) (surjective : Function.Surjective q)

/-- The set of orbits under the kernel of a surjective group map. -/
abbrev Fiber (A : Type u) [MulAction Pi A] :=
  MulAction.orbitRel.Quotient q.toMonoidHom.ker A

noncomputable instance fiberTopology
    (A : Type u) [MulAction Pi A] :
    TopologicalSpace (Fiber q A) :=
  ⊥

instance fiberDiscreteTopology
    (A : Type u) [MulAction Pi A] :
    DiscreteTopology (Fiber q A) :=
  ⟨rfl⟩

/-- The ambient `Pi`-action descends to its kernel-orbit set. -/
noncomputable instance fiberPiAction
    (A : Type u) [MulAction Pi A] :
    MulAction Pi (Fiber q A) where
  smul a z :=
    Quotient.map' (fun x : A => a • x) (by
      intro x y hxy
      rw [MulAction.orbitRel_apply] at hxy ⊢
      obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hxy
      refine MulAction.mem_orbit_iff.mpr
        ⟨⟨a * k * a⁻¹, ?_⟩, ?_⟩
      · change q (a * (k : Pi) * a⁻¹) = 1
        have qk : q (k : Pi) = 1 := MonoidHom.mem_ker.mp k.property
        simp [qk]
      · rw [← hk]
        change (a * (k : Pi) * a⁻¹) • (a • y) = a • ((k : Pi) • y)
        simp [mul_smul]) z
  one_smul z := by
    induction z using Quotient.inductionOn' with
    | _ x => exact congrArg Quotient.mk'' (one_smul Pi x)
  mul_smul a b z := by
    induction z using Quotient.inductionOn' with
    | _ x => exact congrArg Quotient.mk'' (mul_smul a b x)

/-- Elements of `ker(q)` act trivially on the orbit set. -/
theorem kernel_fixes
    (A : Type u) [MulAction Pi A]
    (k : q.toMonoidHom.ker) (z : Fiber q A) :
    (k.1 : Pi) • z = z := by
  induction z using Quotient.inductionOn' with
  | _ x =>
      apply Quotient.sound
      change MulAction.orbitRel q.toMonoidHom.ker A ((k : Pi) • x) x
      rw [MulAction.orbitRel_apply]
      exact MulAction.mem_orbit_iff.mpr ⟨k, rfl⟩

/-- The permutation action on kernel orbits factors through `Pi/ker(q)`. -/
noncomputable def quotientGroupActionHom
    (A : Type u) [MulAction Pi A] :
    Pi ⧸ q.toMonoidHom.ker →* Equiv.Perm (Fiber q A) :=
  QuotientGroup.lift q.toMonoidHom.ker
    (MulAction.toPermHom Pi (Fiber q A)) (by
      intro k hk
      ext z
      change k • z = z
      exact kernel_fixes q A ⟨k, hk⟩ z)

/-- Transport the quotient action across the first-isomorphism equivalence. -/
@[reducible]
noncomputable def targetAction
    (A : Type u) [MulAction Pi A] : MulAction G (Fiber q A) :=
  MulAction.compHom (Fiber q A)
    ((quotientGroupActionHom q A).comp
      (QuotientGroup.quotientKerEquivOfSurjective
        q.toMonoidHom surjective).symm.toMonoidHom)

/-- Restricting the descended action along `q` recovers the action on orbit
representatives. -/
@[simp]
theorem smul_mk
    (A : Type u) [MulAction Pi A] (a : Pi) (x : A) :
    letI := targetAction q surjective A
    q a • (Quotient.mk'' x : Fiber q A) = Quotient.mk'' (a • x) := by
  let equivalence :=
    QuotientGroup.quotientKerEquivOfSurjective
      q.toMonoidHom surjective
  have inverse_map :
      equivalence.symm (q a) =
        (QuotientGroup.mk a : Pi ⧸ q.toMonoidHom.ker) := by
    apply equivalence.injective
    rw [equivalence.apply_symm_apply]
    rfl
  change
    (quotientGroupActionHom q A)
        (equivalence.symm (q a)) (Quotient.mk'' x) =
      Quotient.mk'' (a • x)
  rw [inverse_map]
  change
    (MulAction.toPermHom Pi (Fiber q A) a) (Quotient.mk'' x) =
      Quotient.mk'' (a • x)
  rfl

/-- The descended `G`-action is continuous.  For each orbit class, the image
of the open stabilizer of one representative is an open subgroup fixing that
class. -/
theorem targetContinuous
    [IsTopologicalGroup Pi] [IsTopologicalGroup G]
    (openMap : IsOpenMap q)
    (A : Type u) [TopologicalSpace A] [DiscreteTopology A]
    [MulAction Pi A] [ContinuousSMul Pi A] :
    letI := targetAction q surjective A
    ContinuousSMul G (Fiber q A) := by
  letI := targetAction q surjective A
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro z
  induction z using Quotient.inductionOn' with
  | _ x =>
      let U : Subgroup Pi := MulAction.stabilizer Pi x
      let V : Subgroup G := Subgroup.map q.toMonoidHom U
      have V_open : IsOpen (V : Set G) := by
        change IsOpen (q '' (U : Set Pi))
        exact openMap _ (stabilizer_isOpen Pi x)
      apply Subgroup.isOpen_mono
        (H₁ := V) (H₂ := MulAction.stabilizer G (Quotient.mk'' x)) _ V_open
      intro g hg
      obtain ⟨a, ha, rfl⟩ := hg
      rw [MulAction.mem_stabilizer_iff]
      change q a • (Quotient.mk'' x : Fiber q A) = Quotient.mk'' x
      rw [smul_mk q surjective A]
      exact congrArg Quotient.mk''
        ((MulAction.mem_stabilizer_iff.mp ha))

end SourceKernelOrbit

end Iut
