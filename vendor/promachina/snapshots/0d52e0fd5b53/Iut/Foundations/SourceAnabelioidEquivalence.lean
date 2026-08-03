/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceAnabelioid

/-!
# Pointed equivalences of connected anabelioids

In *The Geometry of Anabelioids*, Proposition 1.1.4, an equivalence of
connected anabelioids induces an isomorphism of profinite fundamental groups,
up to inner automorphism after basepoints are forgotten.  This file derives
the pointed statement from an exact pullback equivalence and its chosen
fiber-functor identification.

The inverse map on fundamental groups is not stored as extra data.  It is
constructed from a quasi-inverse functor.  The two triangle isomorphisms give
2-isomorphisms to the identity; the existing conjugacy theorem then proves
that the derived map is bijective.  Compactness and Hausdorffness upgrade the
resulting algebraic equivalence to a continuous equivalence of profinite
groups.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits

/-- A pointed exact morphism whose contravariant pullback functor is a
categorical equivalence. -/
structure SourcePointedAnabelioidEquivalence
    (source target : EtaleFundamentalGroup.{u})
    extends SourcePointedAnabelioidHom source target where
  pullbackIsEquivalence :
    letI := target.coverCategory
    letI := source.coverCategory
    toSourcePointedAnabelioidHom.pullback.IsEquivalence

namespace SourcePointedAnabelioidEquivalence

variable {source target : EtaleFundamentalGroup.{u}}

/-- The categorical equivalence represented by the pullback functor. -/
noncomputable def coverEquivalence
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    target.Cover ≌ source.Cover := by
  letI := target.coverCategory
  letI := source.coverCategory
  letI : equivalence.toSourcePointedAnabelioidHom.pullback.IsEquivalence :=
    equivalence.pullbackIsEquivalence
  exact equivalence.toSourcePointedAnabelioidHom.pullback.asEquivalence

/-- The fiber-functor identification for the quasi-inverse pullback. -/
noncomputable def inverseFiberIso
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    equivalence.coverEquivalence.inverse ⋙ target.fiber ≅ source.fiber := by
  letI := target.coverCategory
  letI := source.coverCategory
  let e := equivalence.coverEquivalence
  exact
    Functor.isoWhiskerLeft e.inverse
        equivalence.toSourcePointedAnabelioidHom.fiberIso.symm ≪≫
      (Functor.associator e.inverse e.functor source.fiber).symm ≪≫
      Functor.isoWhiskerRight e.counitIso source.fiber ≪≫
      Functor.leftUnitor source.fiber

/-- The pointed morphism carried by a categorical quasi-inverse. -/
noncomputable def inversePointedHom
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    SourcePointedAnabelioidHom target source := by
  letI := target.coverCategory
  letI := source.coverCategory
  let e := equivalence.coverEquivalence
  exact
    { pullback := e.inverse
      preservesFiniteLimits := inferInstance
      preservesFiniteColimits := inferInstance
      fiberIso := equivalence.inverseFiberIso }

/-- The first triangle of the categorical equivalence, regarded as a
2-isomorphism of pointed anabelioid morphisms. -/
noncomputable def homInverseTwoIso
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    SourcePointedAnabelioidHom.TwoIso
      (equivalence.toSourcePointedAnabelioidHom.comp
        equivalence.inversePointedHom)
      (SourcePointedAnabelioidHom.identity source) := by
  letI := target.coverCategory
  letI := source.coverCategory
  exact
    { pullbackIso := equivalence.coverEquivalence.counitIso }

/-- The second triangle of the categorical equivalence, regarded as a
2-isomorphism of pointed anabelioid morphisms. -/
noncomputable def inverseHomTwoIso
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    SourcePointedAnabelioidHom.TwoIso
      (equivalence.inversePointedHom.comp
        equivalence.toSourcePointedAnabelioidHom)
      (SourcePointedAnabelioidHom.identity target) := by
  letI := target.coverCategory
  letI := source.coverCategory
  exact
    { pullbackIso := equivalence.coverEquivalence.unitIso.symm }

/-- A pointed categorical equivalence induces a bijection on the certified
profinite fundamental groups. -/
theorem fundamentalGroupHom_bijective
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    Function.Bijective
      equivalence.toSourcePointedAnabelioidHom.fundamentalGroupHom := by
  constructor
  · intro first second equality
    let inverse := equivalence.inversePointedHom
    let comparison := equivalence.homInverseTwoIso
    have composedEquality :
        (equivalence.toSourcePointedAnabelioidHom.comp inverse
          ).fundamentalGroupHom first =
          (equivalence.toSourcePointedAnabelioidHom.comp inverse
            ).fundamentalGroupHom second := by
      rw [SourcePointedAnabelioidHom.fundamentalGroupHom_comp]
      rw [SourcePointedAnabelioidHom.fundamentalGroupHom_comp]
      exact congrArg inverse.fundamentalGroupHom equality
    have conjugatedEquality :
        comparison.fundamentalGroupTransport *
              (equivalence.toSourcePointedAnabelioidHom.comp inverse
                ).fundamentalGroupHom first *
            comparison.fundamentalGroupTransport⁻¹ =
          comparison.fundamentalGroupTransport *
              (equivalence.toSourcePointedAnabelioidHom.comp inverse
                ).fundamentalGroupHom second *
            comparison.fundamentalGroupTransport⁻¹ :=
      congrArg
        (fun value =>
          comparison.fundamentalGroupTransport * value *
            comparison.fundamentalGroupTransport⁻¹)
        composedEquality
    rw [← comparison.fundamentalGroupHom_eq_conjugate] at conjugatedEquality
    rw [← comparison.fundamentalGroupHom_eq_conjugate] at conjugatedEquality
    simpa only [SourcePointedAnabelioidHom.fundamentalGroupHom_identity]
      using conjugatedEquality
  · intro element
    let inverse := equivalence.inversePointedHom
    let comparison := equivalence.inverseHomTwoIso
    let transport := comparison.fundamentalGroupTransport
    let conjugatedElement := transport * element * transport⁻¹
    refine
      ⟨inverse.fundamentalGroupHom conjugatedElement, ?_⟩
    have comparisonEquality :=
      comparison.fundamentalGroupHom_eq_conjugate conjugatedElement
    rw [SourcePointedAnabelioidHom.fundamentalGroupHom_identity]
      at comparisonEquality
    rw [SourcePointedAnabelioidHom.fundamentalGroupHom_comp]
      at comparisonEquality
    dsimp [conjugatedElement, transport] at comparisonEquality ⊢
    have leftCancellation := mul_right_cancel comparisonEquality
    have middleEquality := mul_left_cancel leftCancellation
    simpa only [inverse] using middleEquality.symm

/-- The algebraic fundamental-group equivalence derived from a pointed
categorical equivalence. -/
noncomputable def fundamentalGroupMulEquiv
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    source.group ≃* target.group :=
  MulEquiv.ofBijective
    equivalence.toSourcePointedAnabelioidHom.fundamentalGroupHom.hom
    equivalence.fundamentalGroupHom_bijective

/-- The underlying map of the algebraic equivalence is the derived
fundamental-group homomorphism. -/
theorem fundamentalGroupMulEquiv_apply
    (equivalence : SourcePointedAnabelioidEquivalence source target)
    (element : source.group) :
    equivalence.fundamentalGroupMulEquiv element =
      equivalence.toSourcePointedAnabelioidHom.fundamentalGroupHom element :=
  rfl

/-- The source-faithful profinite-group isomorphism derived from a pointed
categorical equivalence. -/
noncomputable def fundamentalGroupContinuousMulEquiv
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    source.group ≃ₜ* target.group where
  toMulEquiv := equivalence.fundamentalGroupMulEquiv
  continuous_toFun := by
    exact equivalence.toSourcePointedAnabelioidHom.fundamentalGroupContinuousHom.continuous
  continuous_invFun := by
    exact Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := equivalence.fundamentalGroupMulEquiv.toEquiv)
      equivalence.toSourcePointedAnabelioidHom.fundamentalGroupContinuousHom.continuous

/-- The underlying map of the derived profinite equivalence is exactly the
map induced by the pointed anabelioid equivalence. -/
theorem fundamentalGroupContinuousMulEquiv_apply
    (equivalence : SourcePointedAnabelioidEquivalence source target)
    (element : source.group) :
    equivalence.fundamentalGroupContinuousMulEquiv element =
      equivalence.toSourcePointedAnabelioidHom.fundamentalGroupHom element :=
  rfl

end SourcePointedAnabelioidEquivalence

end Iut
