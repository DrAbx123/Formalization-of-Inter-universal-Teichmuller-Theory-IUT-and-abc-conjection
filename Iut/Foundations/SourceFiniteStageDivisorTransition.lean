/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageValuationDivisor

/-!
# Ramification-weighted divisor transitions between finite stages

For every inclusion of finite Galois reconstruction stages, this file builds
the induced map on canonical value groups and conjugates it through the two
discrete normalizations `ValueGroupWithZero ≃*o ℤᵐ⁰`.  The resulting additive
map on `ℤ` is multiplication by a positive ramification index.  It therefore
restricts to an injective divisor pullback on `ℕ`.

The value-group, additive, unit, and divisor transitions are proved to satisfy
identity and composition.  In particular, normalized additive valuation is
natural for the genuine intermediate-field inclusion; no equality between the
independently chosen stage normalizations is assumed.
-/

open ValuativeRel
open scoped NNReal NormedField WithZero

namespace Iut.SourceFinitePlaceReconstruction

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

@[reducible]
noncomputable def stageInclusionAlgebra
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    Algebra source target :=
  (IntermediateField.inclusion map).toAlgebra

theorem stageInclusionValuativeExtension
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    letI : Algebra source target := stageInclusionAlgebra place map
    ValuativeExtension source target := by
  letI : Algebra source target := stageInclusionAlgebra place map
  constructor
  intro first second
  change
    ‖algebraMap source target first‖₊ ≤
        ‖algebraMap source target second‖₊ ↔
      ‖first‖₊ ≤ ‖second‖₊
  rfl

noncomputable def stageNormalizedValueGroupTransition
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    ℤᵐ⁰ →*₀ ℤᵐ⁰ := by
  letI : Algebra source target := stageInclusionAlgebra place map
  letI : ValuativeExtension source target :=
    stageInclusionValuativeExtension place map
  exact
    (stageValueGroupWithZeroIsoInt place target).toMonoidWithZeroHom.comp
      ((ValuativeExtension.mapValueGroupWithZero source target).comp
        (stageValueGroupWithZeroIsoInt place source).symm.toMonoidWithZeroHom)

theorem stageNormalizedValueGroupTransition_strictMono
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    StrictMono (stageNormalizedValueGroupTransition place map) := by
  letI : Algebra source target := stageInclusionAlgebra place map
  letI : ValuativeExtension source target :=
    stageInclusionValuativeExtension place map
  exact
    (stageValueGroupWithZeroIsoInt place target).strictMono.comp
      (ValuativeExtension.mapValueGroupWithZero_strictMono.comp
        (stageValueGroupWithZeroIsoInt place source).symm.strictMono)

theorem stageNormalizedValueGroupTransition_valuation
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target)
    (value : source) :
    stageNormalizedValueGroupTransition place map
        (stageValueGroupWithZeroIsoInt place source
          (ValuativeRel.valuation source value)) =
      stageValueGroupWithZeroIsoInt place target
        (ValuativeRel.valuation target
          (IntermediateField.inclusion map value)) := by
  letI : Algebra source target := stageInclusionAlgebra place map
  letI : ValuativeExtension source target :=
    stageInclusionValuativeExtension place map
  rw [stageNormalizedValueGroupTransition]
  simp only [MonoidWithZeroHom.comp_apply]
  change
    stageValueGroupWithZeroIsoInt place target
        (ValuativeExtension.mapValueGroupWithZero source target
          ((stageValueGroupWithZeroIsoInt place source).symm
            (stageValueGroupWithZeroIsoInt place source
              (ValuativeRel.valuation source value)))) =
      stageValueGroupWithZeroIsoInt place target
        (ValuativeRel.valuation target
          (IntermediateField.inclusion map value))
  rw [(stageValueGroupWithZeroIsoInt place source).symm_apply_apply]
  rw [ValuativeExtension.mapValueGroupWithZero_valuation]
  rfl

noncomputable def stageNormalizedAdditiveTransition
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    ℤ →+ ℤ where
  toFun exponent :=
    WithZero.log
      (stageNormalizedValueGroupTransition place map
        (WithZero.exp exponent))
  map_zero' := by
    simp
  map_add' := by
    intro first second
    change
      WithZero.log
          (stageNormalizedValueGroupTransition place map
            (WithZero.exp (first + second))) =
        WithZero.log
            (stageNormalizedValueGroupTransition place map
              (WithZero.exp first)) +
          WithZero.log
            (stageNormalizedValueGroupTransition place map
              (WithZero.exp second))
    rw [WithZero.exp_add, map_mul, WithZero.log_mul]
    · exact
        (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
          WithZero.exp_ne_zero
    · exact
        (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
          WithZero.exp_ne_zero

theorem stageNormalizedAdditiveTransition_strictMono
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    StrictMono (stageNormalizedAdditiveTransition place map) := by
  intro first second first_lt_second
  change
    WithZero.log
        (stageNormalizedValueGroupTransition place map
          (WithZero.exp first)) <
      WithZero.log
        (stageNormalizedValueGroupTransition place map
          (WithZero.exp second))
  rw [WithZero.log_lt_log]
  · exact
      stageNormalizedValueGroupTransition_strictMono place map
        (WithZero.exp_lt_exp.mpr first_lt_second)
  · exact
      (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
        WithZero.exp_ne_zero
  · exact
      (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
        WithZero.exp_ne_zero

theorem stageNormalizedAdditiveTransition_one_pos
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    0 < stageNormalizedAdditiveTransition place map 1 := by
  have comparison :=
    stageNormalizedAdditiveTransition_strictMono place map
      (show (0 : ℤ) < 1 by exact Int.zero_lt_one)
  simpa using comparison

noncomputable def stageRamificationIndex
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) : ℕ :=
  Int.toNat (stageNormalizedAdditiveTransition place map 1)

theorem stageRamificationIndex_pos
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    0 < stageRamificationIndex place map := by
  let value := stageNormalizedAdditiveTransition place map 1
  have value_pos : 0 < value :=
    stageNormalizedAdditiveTransition_one_pos place map
  apply Nat.pos_of_ne_zero
  intro equality
  have value_eq_zero : value = 0 := by
    calc
      value = (Int.toNat value : ℤ) :=
        (Int.toNat_of_nonneg value_pos.le).symm
      _ = 0 := by
        rw [show Int.toNat value = 0 by
          simpa [stageRamificationIndex, value] using equality]
        rfl
  exact value_pos.ne' value_eq_zero

noncomputable def stageDivisorPullback
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    ℕ →+ ℕ :=
  AddMonoidHom.mulLeft (stageRamificationIndex place map)

noncomputable def stageUnitTransition
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    sourceˣ →* targetˣ :=
  Units.map (IntermediateField.inclusion map).toMonoidHom

theorem stageUnitTransition_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    stageUnitTransition place (show stage ≤ stage from le_rfl) =
      MonoidHom.id stageˣ := by
  apply MonoidHom.ext
  intro unit
  apply Units.ext
  rfl

theorem stageUnitTransition_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    (stageUnitTransition place secondThird).comp
        (stageUnitTransition place firstSecond) =
      stageUnitTransition place (firstSecond.trans secondThird) := by
  apply MonoidHom.ext
  intro unit
  apply Units.ext
  rfl

theorem stageUnitTransition_injective
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    Function.Injective (stageUnitTransition place map) := by
  intro first second equality
  apply Units.ext
  apply (IntermediateField.inclusion map).injective
  exact congrArg Units.val equality

theorem stageNormalizedAdditiveValuation_transition
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target)
    (unit : sourceˣ) :
    stageNormalizedAdditiveValuation place target
        (Additive.ofMul (stageUnitTransition place map unit)) =
      stageNormalizedAdditiveTransition place map
        (stageNormalizedAdditiveValuation place source
          (Additive.ofMul unit)) := by
  let sourceValue :=
    stageValueGroupWithZeroIsoInt place source
      (ValuativeRel.valuation source unit.1)
  have sourceValue_ne_zero : sourceValue ≠ 0 := by
    simp [sourceValue]
  change
    -WithZero.log
        (stageValueGroupWithZeroIsoInt place target
          (ValuativeRel.valuation target
            (IntermediateField.inclusion map unit.1))) =
      WithZero.log
        (stageNormalizedValueGroupTransition place map
          (WithZero.exp (-WithZero.log sourceValue)))
  rw [← stageNormalizedValueGroupTransition_valuation
    place map unit.1]
  change
    -WithZero.log
        (stageNormalizedValueGroupTransition place map sourceValue) =
      WithZero.log
        (stageNormalizedValueGroupTransition place map
          (WithZero.exp (-WithZero.log sourceValue)))
  rw [WithZero.exp_neg, WithZero.exp_log sourceValue_ne_zero,
    map_inv₀, WithZero.log_inv]

theorem stageNormalizedValueGroupTransition_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    stageNormalizedValueGroupTransition place
        (show stage ≤ stage from le_rfl) =
      MonoidWithZeroHom.id ℤᵐ⁰ := by
  apply MonoidWithZeroHom.ext
  intro value
  obtain ⟨stageValue, stageValue_eq⟩ :=
    ValuativeRel.valuation_surjective
      (K := stage)
      ((stageValueGroupWithZeroIsoInt place stage).symm value)
  have coordinate_eq :
      stageValueGroupWithZeroIsoInt place stage
          (ValuativeRel.valuation stage stageValue) = value := by
    rw [stageValue_eq]
    exact
      (stageValueGroupWithZeroIsoInt place stage).apply_symm_apply value
  rw [← coordinate_eq,
    stageNormalizedValueGroupTransition_valuation]
  rfl

theorem stageNormalizedValueGroupTransition_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    (stageNormalizedValueGroupTransition place secondThird).comp
        (stageNormalizedValueGroupTransition place firstSecond) =
      stageNormalizedValueGroupTransition place
        (firstSecond.trans secondThird) := by
  apply MonoidWithZeroHom.ext
  intro value
  obtain ⟨stageValue, stageValue_eq⟩ :=
    ValuativeRel.valuation_surjective
      (K := first)
      ((stageValueGroupWithZeroIsoInt place first).symm value)
  have coordinate_eq :
      stageValueGroupWithZeroIsoInt place first
          (ValuativeRel.valuation first stageValue) = value := by
    rw [stageValue_eq]
    exact
      (stageValueGroupWithZeroIsoInt place first).apply_symm_apply value
  rw [← coordinate_eq, MonoidWithZeroHom.comp_apply,
    stageNormalizedValueGroupTransition_valuation,
    stageNormalizedValueGroupTransition_valuation,
    stageNormalizedValueGroupTransition_valuation]
  rfl

theorem stageNormalizedAdditiveTransition_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    stageNormalizedAdditiveTransition place
        (show stage ≤ stage from le_rfl) =
      AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext
  intro exponent
  change
    WithZero.log
        (stageNormalizedValueGroupTransition place le_rfl
          (WithZero.exp exponent)) = exponent
  rw [stageNormalizedValueGroupTransition_refl]
  simp

theorem stageNormalizedAdditiveTransition_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    (stageNormalizedAdditiveTransition place secondThird).comp
        (stageNormalizedAdditiveTransition place firstSecond) =
      stageNormalizedAdditiveTransition place
        (firstSecond.trans secondThird) := by
  apply AddMonoidHom.ext
  intro exponent
  let middleValue :=
    stageNormalizedValueGroupTransition place firstSecond
      (WithZero.exp exponent)
  have middleValue_ne_zero : middleValue ≠ 0 := by
    exact
      (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
        WithZero.exp_ne_zero
  change
    WithZero.log
        (stageNormalizedValueGroupTransition place secondThird
          (WithZero.exp (WithZero.log middleValue))) =
      WithZero.log
        (stageNormalizedValueGroupTransition place
          (firstSecond.trans secondThird) (WithZero.exp exponent))
  rw [WithZero.exp_log middleValue_ne_zero]
  change
    WithZero.log
        (((stageNormalizedValueGroupTransition place secondThird).comp
          (stageNormalizedValueGroupTransition place firstSecond))
            (WithZero.exp exponent)) =
      WithZero.log
        (stageNormalizedValueGroupTransition place
          (firstSecond.trans secondThird) (WithZero.exp exponent))
  rw [stageNormalizedValueGroupTransition_trans]

theorem stageNormalizedAdditiveTransition_eq_ramification_mul
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target)
    (exponent : ℤ) :
    stageNormalizedAdditiveTransition place map exponent =
      (stageRamificationIndex place map : ℤ) * exponent := by
  let transition := stageNormalizedAdditiveTransition place map
  have one_nonnegative : 0 ≤ transition 1 :=
    (stageNormalizedAdditiveTransition_one_pos place map).le
  have mapped := map_zsmul transition exponent (1 : ℤ)
  change transition (exponent • (1 : ℤ)) =
    exponent • transition 1 at mapped
  calc
    transition exponent = exponent * transition 1 := by
      simpa using mapped
    _ = (stageRamificationIndex place map : ℤ) * exponent := by
      rw [stageRamificationIndex,
        Int.toNat_of_nonneg one_nonnegative]
      exact mul_comm _ _

theorem stageRamificationIndex_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    stageRamificationIndex place
        (show stage ≤ stage from le_rfl) = 1 := by
  rw [stageRamificationIndex]
  have equality := DFunLike.congr_fun
    (stageNormalizedAdditiveTransition_refl place stage) 1
  simpa using congrArg Int.toNat equality

theorem stageRamificationIndex_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    stageRamificationIndex place
        (firstSecond.trans secondThird) =
      stageRamificationIndex place firstSecond *
        stageRamificationIndex place secondThird := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul]
  have transitionEquality := DFunLike.congr_fun
    (stageNormalizedAdditiveTransition_trans
      place firstSecond secondThird) 1
  rw [AddMonoidHom.comp_apply,
    stageNormalizedAdditiveTransition_eq_ramification_mul,
    stageNormalizedAdditiveTransition_eq_ramification_mul,
    stageNormalizedAdditiveTransition_eq_ramification_mul,
    mul_one] at transitionEquality
  simpa [mul_comm] using transitionEquality.symm

theorem stageDivisorPullback_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    stageDivisorPullback place
        (show stage ≤ stage from le_rfl) =
      AddMonoidHom.id ℕ := by
  apply AddMonoidHom.ext
  intro value
  simp [stageDivisorPullback,
    stageRamificationIndex_refl]

theorem stageDivisorPullback_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    stageDivisorPullback place
        (source := first) (target := third)
        (firstSecond.trans secondThird) =
      (stageDivisorPullback place
        (source := second) (target := third) secondThird).comp
        (stageDivisorPullback place
          (source := first) (target := second) firstSecond) := by
  apply AddMonoidHom.ext
  intro value
  change
    stageRamificationIndex place
          (firstSecond.trans secondThird) * value =
      stageRamificationIndex place secondThird *
        (stageRamificationIndex place firstSecond * value)
  rw [stageRamificationIndex_trans
    place firstSecond secondThird]
  ac_rfl

theorem stageDivisorPullback_injective
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    Function.Injective (stageDivisorPullback place map) := by
  intro first second equality
  exact mul_left_cancel₀
    (Nat.ne_of_gt (stageRamificationIndex_pos place map)) equality

end

end Iut.SourceFinitePlaceReconstruction
