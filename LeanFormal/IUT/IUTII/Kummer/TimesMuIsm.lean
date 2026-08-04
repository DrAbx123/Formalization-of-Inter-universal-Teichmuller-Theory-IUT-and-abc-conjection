/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import Mathlib.Topology.Algebra.OpenSubgroup

namespace LeanFormal.IUT

/-!
  The algebraic `Ism` and orbit layer of IUT II, Definition 4.9(i).

  This module is adapted from the Definition 4.9(i) kernel in
  `promachina/iut-lean`, `SourceThetaEvaluation.lean`, last changed by upstream
  commit `3de1d7c1`, under Apache-2.0.  It is parameterized by honest Mathlib
  group actions and uses the torsion quotient constructed in
  `TimesMuQuotient.lean`.

  No isomorphism between the paper's group-theoretic `O^xmu(G)` and a
  Frobenioid evaluation is asserted to exist here.  If such an isomorphism is
  supplied, the definitions below prove that its invariant-image conditions
  determine one unique `Ism` orbit.
-/

universe uG uU uW

namespace TimesMuKummer

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {U : Type uU} [CommGroup U]
variable {W : Type uW} [CommGroup W]

def fixedSubgroup (rho : G →* MulAut U) (H : OpenSubgroup G) : Subgroup U where
  carrier := {u | ∀ g : H, rho (g : G) u = u}
  one_mem' := fun _ ↦ map_one _
  mul_mem' := by
    intro first second hfirst hsecond g
    rw [map_mul, hfirst g, hsecond g]
  inv_mem' := by
    intro u hu g
    rw [map_inv, hu g]

@[simp] theorem mem_fixedSubgroup_iff
    (rho : G →* MulAut U) (H : OpenSubgroup G) (u : U) :
    u ∈ fixedSubgroup rho H ↔ ∀ g : H, rho (g : G) u = u := Iff.rfl

def invariantImage (rho : G →* MulAut U) (H : OpenSubgroup G) :
    Subgroup (TimesMuQuotient U) :=
  (fixedSubgroup rho H).map TimesMuQuotient.quotientMap

theorem mem_invariantImage_iff
    (rho : G →* MulAut U) (H : OpenSubgroup G)
    (x : TimesMuQuotient U) :
    x ∈ invariantImage rho H ↔
      ∃ u : U, (∀ g : H, rho (g : G) u = u) ∧
        TimesMuQuotient.quotientMap u = x := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem invariantImage_fixed
    (rho : G →* MulAut U) (H : OpenSubgroup G)
    {x : TimesMuQuotient U} (hx : x ∈ invariantImage rho H) (g : H) :
    TimesMuQuotient.action rho (g : G) x = x := by
  rcases (mem_invariantImage_iff rho H x).mp hx with ⟨u, hu, rfl⟩
  rw [TimesMuQuotient.action_quotientMap, hu g]

def IsKummerIsometry
    (rho : G →* MulAut U) (automorphism : MulAut (TimesMuQuotient U)) : Prop :=
  (∀ g x,
      automorphism (TimesMuQuotient.action rho g x) =
        TimesMuQuotient.action rho g (automorphism x)) ∧
    ∀ H,
      automorphism '' (invariantImage rho H : Set (TimesMuQuotient U)) =
        (invariantImage rho H : Set (TimesMuQuotient U))

def ismSubgroup (rho : G →* MulAut U) :
    Subgroup (MulAut (TimesMuQuotient U)) where
  carrier := IsKummerIsometry rho
  one_mem' := by
    constructor
    · intro g x
      rfl
    · intro H
      ext x
      change (∃ source ∈ invariantImage rho H, source = x) ↔
        x ∈ invariantImage rho H
      simp
  mul_mem' := by
    intro first second hfirst hsecond
    constructor
    · intro g x
      change first (second (TimesMuQuotient.action rho g x)) =
        TimesMuQuotient.action rho g (first (second x))
      rw [hsecond.1, hfirst.1]
    · intro H
      ext x
      constructor
      · rintro ⟨source, hsource, hvalue⟩
        change first (second source) = x at hvalue
        have hsecondSource : second source ∈
            (invariantImage rho H : Set (TimesMuQuotient U)) := by
          have : second source ∈
              second '' (invariantImage rho H : Set (TimesMuQuotient U)) :=
            ⟨source, hsource, rfl⟩
          simpa only [hsecond.2 H] using this
        have hfirstSource : first (second source) ∈
            (invariantImage rho H : Set (TimesMuQuotient U)) := by
          have : first (second source) ∈
              first '' (invariantImage rho H : Set (TimesMuQuotient U)) :=
            ⟨second source, hsecondSource, rfl⟩
          simpa only [hfirst.2 H] using this
        rwa [hvalue] at hfirstSource
      · intro hvalue
        have hfirstImage : x ∈
            first '' (invariantImage rho H : Set (TimesMuQuotient U)) := by
          simpa only [hfirst.2 H] using hvalue
        rcases hfirstImage with ⟨middle, hmiddle, rfl⟩
        have hsecondImage : middle ∈
            second '' (invariantImage rho H : Set (TimesMuQuotient U)) := by
          simpa only [hsecond.2 H] using hmiddle
        rcases hsecondImage with ⟨source, hsource, rfl⟩
        exact ⟨source, hsource, rfl⟩
  inv_mem' := by
    intro automorphism hautomorphism
    constructor
    · intro g x
      apply automorphism.injective
      change automorphism (automorphism.symm (TimesMuQuotient.action rho g x)) =
        automorphism
          (TimesMuQuotient.action rho g (automorphism.symm x))
      rw [automorphism.apply_symm_apply]
      rw [hautomorphism.1 g (automorphism.symm x)]
      rw [automorphism.apply_symm_apply]
    · intro H
      ext x
      constructor
      · rintro ⟨source, hsource, rfl⟩
        change automorphism.symm source ∈ invariantImage rho H
        have himage : source ∈
            automorphism '' (invariantImage rho H : Set (TimesMuQuotient U)) := by
          simpa only [hautomorphism.2 H] using hsource
        rcases himage with ⟨preimage, hpreimage, heq⟩
        have hinverse : automorphism.symm source = preimage := by
          rw [← heq, automorphism.symm_apply_apply]
        rwa [hinverse]
      · intro hvalue
        refine ⟨automorphism x, ?_, automorphism.symm_apply_apply x⟩
        have : automorphism x ∈
            automorphism '' (invariantImage rho H : Set (TimesMuQuotient U)) :=
          ⟨x, hvalue, rfl⟩
        simpa only [hautomorphism.2 H] using this

abbrev Ism (rho : G →* MulAut U) := ismSubgroup rho

structure Isomorphism
    (source : G →* MulAut U) (target : G →* MulAut W) where
  equiv : TimesMuQuotient U ≃* TimesMuQuotient W
  equivariant :
    ∀ g x,
      equiv (TimesMuQuotient.action source g x) =
        TimesMuQuotient.action target g (equiv x)
  invariantImage :
    ∀ H,
      equiv '' (TimesMuKummer.invariantImage source H : Set (TimesMuQuotient U)) =
        (TimesMuKummer.invariantImage target H : Set (TimesMuQuotient W))

namespace Isomorphism

@[ext] theorem ext
    {source : G →* MulAut U} {target : G →* MulAut W}
    (first second : Isomorphism source target)
    (equiv_eq : first.equiv = second.equiv) : first = second := by
  cases first
  cases second
  cases equiv_eq
  rfl

def refl (rho : G →* MulAut U) : Isomorphism rho rho where
  equiv := MulEquiv.refl _
  equivariant _ _ := rfl
  invariantImage _ := by
    ext x
    simp

def precompose
    {source : G →* MulAut U} {target : G →* MulAut W}
    (isometry : Ism source) (comparison : Isomorphism source target) :
    Isomorphism source target := by
  let inverse : Ism source := isometry⁻¹
  refine
    { equiv := inverse.1.trans comparison.equiv
      equivariant := ?_
      invariantImage := ?_ }
  · intro g x
    change comparison.equiv
        (inverse.1 (TimesMuQuotient.action source g x)) =
      TimesMuQuotient.action target g (comparison.equiv (inverse.1 x))
    rw [inverse.property.1]
    exact comparison.equivariant g (inverse.1 x)
  · intro H
    change (comparison.equiv ∘ inverse.1) ''
        (TimesMuKummer.invariantImage source H : Set (TimesMuQuotient U)) =
      (TimesMuKummer.invariantImage target H : Set (TimesMuQuotient W))
    rw [Set.image_comp, inverse.property.2 H, comparison.invariantImage H]

@[implicit_reducible] def mulAction
    (source : G →* MulAut U) (target : G →* MulAut W) :
    MulAction (Ism source) (Isomorphism source target) where
  smul := precompose
  one_smul comparison := by
    apply ext
    apply MulEquiv.ext
    intro x
    rfl
  mul_smul first second comparison := by
    apply ext
    apply MulEquiv.ext
    intro x
    rfl

def sourceDifference
    {source : G →* MulAut U} {target : G →* MulAut W}
    (first second : Isomorphism source target) : Ism source := by
  refine ⟨first.equiv.trans second.equiv.symm, ?_⟩
  constructor
  · intro g x
    apply second.equiv.injective
    change second.equiv
        (second.equiv.symm
          (first.equiv (TimesMuQuotient.action source g x))) =
      second.equiv
        (TimesMuQuotient.action source g
          (second.equiv.symm (first.equiv x)))
    rw [second.equiv.apply_symm_apply]
    rw [first.equivariant]
    rw [second.equivariant]
    rw [second.equiv.apply_symm_apply]
  · intro H
    change (second.equiv.symm ∘ first.equiv) ''
        (TimesMuKummer.invariantImage source H : Set (TimesMuQuotient U)) =
      (TimesMuKummer.invariantImage source H : Set (TimesMuQuotient U))
    rw [Set.image_comp, first.invariantImage H, ← second.invariantImage H]
    exact Equiv.symm_image_image second.equiv.toEquiv _

theorem sourceDifference_smul_first
    {source : G →* MulAut U} {target : G →* MulAut W}
    (first second : Isomorphism source target) :
    letI := mulAction source target
    sourceDifference first second • first = second := by
  letI := mulAction source target
  apply ext
  apply MulEquiv.ext
  intro x
  change first.equiv ((first.equiv.trans second.equiv.symm).symm x) =
    second.equiv x
  simp

noncomputable instance
    {source : G →* MulAut U} {target : G →* MulAut W} :
    MulAction (Ism source) (Isomorphism source target) :=
  mulAction source target

abbrev Orbit
    (source : G →* MulAut U) (target : G →* MulAut W) :=
  MulAction.orbitRel.Quotient (Ism source) (Isomorphism source target)

noncomputable def orbitOf
    {source : G →* MulAut U} {target : G →* MulAut W}
    (comparison : Isomorphism source target) : Orbit source target :=
  Quotient.mk'' comparison

theorem orbitOf_eq
    {source : G →* MulAut U} {target : G →* MulAut W}
    (first second : Isomorphism source target) :
    orbitOf first = orbitOf second := by
  apply Quotient.sound
  change first ∈ MulAction.orbit (Ism source) second
  rw [MulAction.mem_orbit_iff]
  exact ⟨sourceDifference second first,
    sourceDifference_smul_first second first⟩

end Isomorphism

end TimesMuKummer

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def timesMuIsm : Obligation :=
  { id := "IUT-II.times-mu-ism-orbit"
    source := "IUT II, Example 1.8(iv); Definition 4.9(i)"
    status := VerificationStatus.proved
    note :=
      "For actual group actions, every open-subgroup fixed-unit image, the exact " ++
        "equivariant image-preserving Ism subgroup, its action on compatible " ++
        "Kummer isomorphisms, and uniqueness of the resulting orbit are constructed " ++
        "and proved. Existence of the paper's group/Frobenioid Kummer isomorphism " ++
        "and its ind-topology are not asserted."
    dependsOn := ["IUT-II.times-mu-torsion-quotient"] }

end LeanFormal.IUT.Audit
