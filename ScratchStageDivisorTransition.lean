import Iut.Foundations.SourceFiniteStageValuationDivisor

open ValuativeRel
open scoped NNReal NormedField WithZero

namespace Iut.SourceFinitePlaceReconstruction

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

@[reducible]
noncomputable def scratchStageAlgebra
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    Algebra source target :=
  (IntermediateField.inclusion map).toAlgebra

theorem scratchStageValuativeExtension
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    letI : Algebra source target := scratchStageAlgebra place map
    ValuativeExtension source target := by
  letI : Algebra source target := scratchStageAlgebra place map
  constructor
  intro first second
  change
    ‖algebraMap source target first‖₊ ≤
        ‖algebraMap source target second‖₊ ↔
      ‖first‖₊ ≤ ‖second‖₊
  rfl

noncomputable def scratchNormalizedValueGroupTransition
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    ℤᵐ⁰ →*₀ ℤᵐ⁰ := by
  letI : Algebra source target := scratchStageAlgebra place map
  letI : ValuativeExtension source target :=
    scratchStageValuativeExtension place map
  exact
    (stageValueGroupWithZeroIsoInt place target).toMonoidWithZeroHom.comp
      ((ValuativeExtension.mapValueGroupWithZero source target).comp
        (stageValueGroupWithZeroIsoInt place source).symm.toMonoidWithZeroHom)

theorem scratchNormalizedValueGroupTransition_strictMono
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    StrictMono (scratchNormalizedValueGroupTransition place map) := by
  letI : Algebra source target := scratchStageAlgebra place map
  letI : ValuativeExtension source target :=
    scratchStageValuativeExtension place map
  exact
    (stageValueGroupWithZeroIsoInt place target).strictMono.comp
      (ValuativeExtension.mapValueGroupWithZero_strictMono.comp
        (stageValueGroupWithZeroIsoInt place source).symm.strictMono)

theorem scratchNormalizedValueGroupTransition_valuation
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target)
    (value : source) :
    scratchNormalizedValueGroupTransition place map
        (stageValueGroupWithZeroIsoInt place source
          (ValuativeRel.valuation source value)) =
      stageValueGroupWithZeroIsoInt place target
        (ValuativeRel.valuation target
          (IntermediateField.inclusion map value)) := by
  letI : Algebra source target := scratchStageAlgebra place map
  letI : ValuativeExtension source target :=
    scratchStageValuativeExtension place map
  rw [scratchNormalizedValueGroupTransition]
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

noncomputable def scratchNormalizedAdditiveTransition
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    ℤ →+ ℤ where
  toFun exponent :=
    WithZero.log
      (scratchNormalizedValueGroupTransition place map
        (WithZero.exp exponent))
  map_zero' := by
    simp
  map_add' := by
    intro first second
    change
      WithZero.log
          (scratchNormalizedValueGroupTransition place map
            (WithZero.exp (first + second))) =
        WithZero.log
            (scratchNormalizedValueGroupTransition place map
              (WithZero.exp first)) +
          WithZero.log
            (scratchNormalizedValueGroupTransition place map
              (WithZero.exp second))
    rw [WithZero.exp_add, map_mul, WithZero.log_mul]
    · exact
        (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
          WithZero.exp_ne_zero
    · exact
        (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
          WithZero.exp_ne_zero

theorem scratchNormalizedAdditiveTransition_strictMono
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    StrictMono (scratchNormalizedAdditiveTransition place map) := by
  intro first second first_lt_second
  change
    WithZero.log
        (scratchNormalizedValueGroupTransition place map
          (WithZero.exp first)) <
      WithZero.log
        (scratchNormalizedValueGroupTransition place map
          (WithZero.exp second))
  rw [WithZero.log_lt_log]
  · exact
      scratchNormalizedValueGroupTransition_strictMono place map
        (WithZero.exp_lt_exp.mpr first_lt_second)
  · exact
      (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
        WithZero.exp_ne_zero
  · exact
      (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
        WithZero.exp_ne_zero

theorem scratchNormalizedAdditiveTransition_one_pos
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    0 < scratchNormalizedAdditiveTransition place map 1 := by
  have comparison :=
    scratchNormalizedAdditiveTransition_strictMono place map
      (show (0 : ℤ) < 1 by exact Int.zero_lt_one)
  simpa using comparison

noncomputable def scratchStageRamificationIndex
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) : ℕ :=
  Int.toNat (scratchNormalizedAdditiveTransition place map 1)

theorem scratchStageRamificationIndex_pos
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    0 < scratchStageRamificationIndex place map := by
  let value := scratchNormalizedAdditiveTransition place map 1
  have value_pos : 0 < value :=
    scratchNormalizedAdditiveTransition_one_pos place map
  apply Nat.pos_of_ne_zero
  intro equality
  have value_eq_zero : value = 0 := by
    calc
      value = (Int.toNat value : ℤ) :=
        (Int.toNat_of_nonneg value_pos.le).symm
      _ = 0 := by
        rw [show Int.toNat value = 0 by
          simpa [scratchStageRamificationIndex, value] using equality]
        rfl
  exact value_pos.ne' value_eq_zero

noncomputable def scratchStageDivisorPullback
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    ℕ →+ ℕ :=
  AddMonoidHom.mulLeft (scratchStageRamificationIndex place map)

noncomputable def scratchStageUnitTransition
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    sourceˣ →* targetˣ :=
  Units.map (IntermediateField.inclusion map).toMonoidHom

theorem scratchStageNormalizedAdditiveValuation_transition
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target)
    (unit : sourceˣ) :
    stageNormalizedAdditiveValuation place target
        (Additive.ofMul (scratchStageUnitTransition place map unit)) =
      scratchNormalizedAdditiveTransition place map
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
        (scratchNormalizedValueGroupTransition place map
          (WithZero.exp (-WithZero.log sourceValue)))
  rw [← scratchNormalizedValueGroupTransition_valuation
    place map unit.1]
  change
    -WithZero.log
        (scratchNormalizedValueGroupTransition place map sourceValue) =
      WithZero.log
        (scratchNormalizedValueGroupTransition place map
          (WithZero.exp (-WithZero.log sourceValue)))
  rw [WithZero.exp_neg, WithZero.exp_log sourceValue_ne_zero,
    map_inv₀, WithZero.log_inv]

theorem scratchNormalizedValueGroupTransition_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    scratchNormalizedValueGroupTransition place
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
    scratchNormalizedValueGroupTransition_valuation]
  rfl

theorem scratchNormalizedValueGroupTransition_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    (scratchNormalizedValueGroupTransition place secondThird).comp
        (scratchNormalizedValueGroupTransition place firstSecond) =
      scratchNormalizedValueGroupTransition place
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
    scratchNormalizedValueGroupTransition_valuation,
    scratchNormalizedValueGroupTransition_valuation,
    scratchNormalizedValueGroupTransition_valuation]
  rfl

theorem scratchNormalizedAdditiveTransition_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    scratchNormalizedAdditiveTransition place
        (show stage ≤ stage from le_rfl) =
      AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext
  intro exponent
  change
    WithZero.log
        (scratchNormalizedValueGroupTransition place le_rfl
          (WithZero.exp exponent)) = exponent
  rw [scratchNormalizedValueGroupTransition_refl]
  simp

theorem scratchNormalizedAdditiveTransition_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    (scratchNormalizedAdditiveTransition place secondThird).comp
        (scratchNormalizedAdditiveTransition place firstSecond) =
      scratchNormalizedAdditiveTransition place
        (firstSecond.trans secondThird) := by
  apply AddMonoidHom.ext
  intro exponent
  let middleValue :=
    scratchNormalizedValueGroupTransition place firstSecond
      (WithZero.exp exponent)
  have middleValue_ne_zero : middleValue ≠ 0 := by
    exact
      (MonoidWithZeroHom.map_eq_zero_iff.not).mpr
        WithZero.exp_ne_zero
  change
    WithZero.log
        (scratchNormalizedValueGroupTransition place secondThird
          (WithZero.exp (WithZero.log middleValue))) =
      WithZero.log
        (scratchNormalizedValueGroupTransition place
          (firstSecond.trans secondThird) (WithZero.exp exponent))
  rw [WithZero.exp_log middleValue_ne_zero]
  change
    WithZero.log
        (((scratchNormalizedValueGroupTransition place secondThird).comp
          (scratchNormalizedValueGroupTransition place firstSecond))
            (WithZero.exp exponent)) =
      WithZero.log
        (scratchNormalizedValueGroupTransition place
          (firstSecond.trans secondThird) (WithZero.exp exponent))
  rw [scratchNormalizedValueGroupTransition_trans]

theorem scratchNormalizedAdditiveTransition_eq_ramification_mul
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target)
    (exponent : ℤ) :
    scratchNormalizedAdditiveTransition place map exponent =
      (scratchStageRamificationIndex place map : ℤ) * exponent := by
  let transition := scratchNormalizedAdditiveTransition place map
  have one_nonnegative : 0 ≤ transition 1 :=
    (scratchNormalizedAdditiveTransition_one_pos place map).le
  have mapped := map_zsmul transition exponent (1 : ℤ)
  change transition (exponent • (1 : ℤ)) =
    exponent • transition 1 at mapped
  calc
    transition exponent = exponent * transition 1 := by
      simpa using mapped
    _ = (scratchStageRamificationIndex place map : ℤ) * exponent := by
      rw [scratchStageRamificationIndex,
        Int.toNat_of_nonneg one_nonnegative]
      exact mul_comm _ _

theorem scratchStageRamificationIndex_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    scratchStageRamificationIndex place
        (show stage ≤ stage from le_rfl) = 1 := by
  rw [scratchStageRamificationIndex]
  have equality := DFunLike.congr_fun
    (scratchNormalizedAdditiveTransition_refl place stage) 1
  simpa using congrArg Int.toNat equality

theorem scratchStageRamificationIndex_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    scratchStageRamificationIndex place
        (firstSecond.trans secondThird) =
      scratchStageRamificationIndex place firstSecond *
        scratchStageRamificationIndex place secondThird := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul]
  have transitionEquality := DFunLike.congr_fun
    (scratchNormalizedAdditiveTransition_trans
      place firstSecond secondThird) 1
  rw [AddMonoidHom.comp_apply,
    scratchNormalizedAdditiveTransition_eq_ramification_mul,
    scratchNormalizedAdditiveTransition_eq_ramification_mul,
    scratchNormalizedAdditiveTransition_eq_ramification_mul,
    mul_one] at transitionEquality
  simpa [mul_comm] using transitionEquality.symm

theorem scratchStageDivisorPullback_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    scratchStageDivisorPullback place
        (show stage ≤ stage from le_rfl) =
      AddMonoidHom.id ℕ := by
  apply AddMonoidHom.ext
  intro value
  simp [scratchStageDivisorPullback,
    scratchStageRamificationIndex_refl]

theorem scratchStageDivisorPullback_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    scratchStageDivisorPullback place
        (source := first) (target := third)
        (firstSecond.trans secondThird) =
      (scratchStageDivisorPullback place
        (source := second) (target := third) secondThird).comp
        (scratchStageDivisorPullback place
          (source := first) (target := second) firstSecond) := by
  apply AddMonoidHom.ext
  intro value
  change
    scratchStageRamificationIndex place
          (firstSecond.trans secondThird) * value =
      scratchStageRamificationIndex place secondThird *
        (scratchStageRamificationIndex place firstSecond * value)
  rw [scratchStageRamificationIndex_trans
    place firstSecond secondThird]
  ac_rfl

theorem scratchStageDivisorPullback_injective
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    Function.Injective (scratchStageDivisorPullback place map) := by
  intro first second equality
  exact mul_left_cancel₀
    (Nat.ne_of_gt (scratchStageRamificationIndex_pos place map)) equality

end

end Iut.SourceFinitePlaceReconstruction
