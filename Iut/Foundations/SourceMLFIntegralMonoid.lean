/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Integral

open scoped nonZeroDivisors

namespace Iut

universe u

noncomputable abbrev SourceMLFAlgebraicIntegerRing
    (K : Type u) [Field K] [ValuativeRel K] :
    Type u :=
  integralClosure
    (Valuation.integer (ValuativeRel.valuation K))
    (AlgebraicClosure K)

noncomputable abbrev SourceMLFIntegralMonoid
    (K : Type u) [Field K] [ValuativeRel K] :
    Type u :=
  (SourceMLFAlgebraicIntegerRing K)⁰

noncomputable abbrev SourceMLFAbsoluteGaloisGroup
    (K : Type u) [Field K] :
    Type u :=
  AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

namespace SourceMLFIntegralMonoid

variable
  (K : Type u) [Field K] [ValuativeRel K]

noncomputable def integralClosureAlgEquiv
    (sigma : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    SourceMLFAlgebraicIntegerRing K ≃+*
      SourceMLFAlgebraicIntegerRing K :=
  ((sigma.restrictScalars
    (Valuation.integer (ValuativeRel.valuation K))).mapIntegralClosure).toRingEquiv

noncomputable def galoisMulAut
    (sigma : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    MulAut (SourceMLFIntegralMonoid K) where
  toFun value :=
    ⟨integralClosureAlgEquiv K sigma value,
      mem_nonZeroDivisors_of_ne_zero
        (by
          rw [← map_zero (integralClosureAlgEquiv K sigma)]
          exact
            (integralClosureAlgEquiv K sigma).injective.ne
              (nonZeroDivisors.coe_ne_zero value))⟩
  invFun value :=
    ⟨integralClosureAlgEquiv K sigma.symm value,
      mem_nonZeroDivisors_of_ne_zero
        (by
          rw [← map_zero (integralClosureAlgEquiv K sigma.symm)]
          exact
            (integralClosureAlgEquiv K sigma.symm).injective.ne
              (nonZeroDivisors.coe_ne_zero value))⟩
  left_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    exact sigma.left_inv value.1.1
  right_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    exact sigma.right_inv value.1.1
  map_mul' first second := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul sigma first.1.1 second.1.1

noncomputable def galoisAction :
    SourceMLFAbsoluteGaloisGroup K →*
      MulAut (SourceMLFIntegralMonoid K) where
  toFun := galoisMulAut K
  map_one' := by
    apply MulEquiv.ext
    intro value
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def absoluteOpenStabilizer
    (value : SourceMLFIntegralMonoid K) :
    OpenSubgroup (SourceMLFAbsoluteGaloisGroup K) := by
  change
    OpenSubgroup
      ((AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K))
  exact
    ⟨MulAction.stabilizer
        ((AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K))
        value.1.1,
      stabilizer_isOpen_of_isIntegral value.1.1⟩

theorem algebraicClosure_isFractionRing :
    IsFractionRing
      (SourceMLFAlgebraicIntegerRing K)
      (AlgebraicClosure K) := by
  let baseRing :=
    Valuation.integer (ValuativeRel.valuation K)
  letI :
      Algebra.IsAlgebraic baseRing (AlgebraicClosure K) :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance :
        Algebra.IsAlgebraic K (AlgebraicClosure K))
  exact
    integralClosure.isFractionRing_of_algebraic
      (fun value equality => by
        apply Subtype.ext
        change (value : K) = 0
        apply (algebraMap K (AlgebraicClosure K)).injective
        change algebraMap K (AlgebraicClosure K) (value : K) = 0 at equality
        simpa only [map_zero] using equality)

noncomputable def toAlgebraicClosureUnits :
    SourceMLFIntegralMonoid K →*
      (AlgebraicClosure K)ˣ where
  toFun value :=
    Units.mk0 value.1.1
      (fun equality =>
        nonZeroDivisors.coe_ne_zero value
          (Subtype.ext equality))
  map_one' := by
    apply Units.ext
    rfl
  map_mul' first second := by
    apply Units.ext
    rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Grothendieck lift synthesis unfolds the nested integral-closure subtype.
noncomputable def groupificationToAlgebraicClosureUnits :
    Algebra.GrothendieckGroup (SourceMLFIntegralMonoid K) →*
      (AlgebraicClosure K)ˣ :=
  Algebra.GrothendieckGroup.lift
    (toAlgebraicClosureUnits K)

set_option synthInstance.maxHeartbeats 200000 in
-- Simplifying the universal lift traverses the nested integral-closure subtype.
@[simp]
theorem groupificationToAlgebraicClosureUnits_of
    (value : SourceMLFIntegralMonoid K) :
    groupificationToAlgebraicClosureUnits K
        (Algebra.GrothendieckGroup.of value) =
      toAlgebraicClosureUnits K value := by
  let universalProperty :=
    Equiv.symm_apply_apply
      (Algebra.GrothendieckGroup.lift
        (M := SourceMLFIntegralMonoid K)
        (G := (AlgebraicClosure K)ˣ))
      (toAlgebraicClosureUnits K)
  change
    (Algebra.GrothendieckGroup.lift
        (toAlgebraicClosureUnits K)).comp
          Algebra.GrothendieckGroup.of =
      toAlgebraicClosureUnits K at universalProperty
  exact DFunLike.congr_fun universalProperty value

theorem grothendieckLift_injective
    {M B : Type u} [CommMonoid M] [CommGroup B]
    (hom : M →* B)
    (hom_injective : Function.Injective hom) :
    Function.Injective
      (Algebra.GrothendieckGroup.lift hom) := by
  letI : IsCancelMul M :=
    hom_injective.isCancelMul hom (map_mul hom)
  change Function.Injective
    ((Localization.monoidOf (⊤ : Submonoid M)).lift
      (fun _ => Group.isUnit _))
  rw [Submonoid.LocalizationMap.lift_injective_iff]
  intro first second
  constructor
  · intro equality
    exact congrArg hom
      (Algebra.GrothendieckGroup.of_injective equality)
  · intro equality
    exact congrArg Algebra.GrothendieckGroup.of
      (hom_injective equality)

set_option synthInstance.maxHeartbeats 200000 in
-- Fraction-ring witnesses require the full integral-closure instance search.
theorem groupificationToAlgebraicClosureUnits_surjective :
    Function.Surjective
      (groupificationToAlgebraicClosureUnits K) := by
  letI :
      IsFractionRing
        (SourceMLFAlgebraicIntegerRing K)
        (AlgebraicClosure K) :=
    algebraicClosure_isFractionRing K
  intro value
  obtain ⟨numerator, denominator, denominatorRegular,
      quotient_eq⟩ :=
    IsFractionRing.div_surjective
      (SourceMLFAlgebraicIntegerRing K)
      (value : AlgebraicClosure K)
  have numerator_ne_zero : numerator ≠ 0 := by
    intro equality
    subst numerator
    have value_eq_zero : (value : AlgebraicClosure K) = 0 := by
      simpa using quotient_eq.symm
    exact value.ne_zero value_eq_zero
  let numeratorMonoid : SourceMLFIntegralMonoid K :=
    ⟨numerator,
      mem_nonZeroDivisors_iff_ne_zero.mpr numerator_ne_zero⟩
  let denominatorMonoid : SourceMLFIntegralMonoid K :=
    ⟨denominator, denominatorRegular⟩
  refine
    ⟨Algebra.GrothendieckGroup.of numeratorMonoid /
        Algebra.GrothendieckGroup.of denominatorMonoid, ?_⟩
  rw [map_div, groupificationToAlgebraicClosureUnits_of,
    groupificationToAlgebraicClosureUnits_of]
  apply Units.ext
  exact quotient_eq

set_option synthInstance.maxHeartbeats 200000 in
-- Grothendieck injectivity unfolds the integral monoid embedding instances.
theorem groupificationToAlgebraicClosureUnits_injective :
    Function.Injective
      (groupificationToAlgebraicClosureUnits K) :=
  grothendieckLift_injective
    (toAlgebraicClosureUnits K) (by
      intro first second equality
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg Units.val equality)

set_option synthInstance.maxHeartbeats 200000 in
-- Building the equivalence synthesizes both preceding Grothendieck proofs.
noncomputable def groupificationEquivAlgebraicClosureUnits :
    Algebra.GrothendieckGroup (SourceMLFIntegralMonoid K) ≃*
      (AlgebraicClosure K)ˣ :=
  MulEquiv.ofBijective
    (groupificationToAlgebraicClosureUnits K)
    ⟨groupificationToAlgebraicClosureUnits_injective K,
      groupificationToAlgebraicClosureUnits_surjective K⟩

end SourceMLFIntegralMonoid

end Iut
