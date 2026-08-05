/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceDefinition52LocalReconstruction
import Iut.Foundations.Frobenioid
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Discrete valuations on finite Galois stages

This file equips every finite Galois stage in the reconstruction of IUT I,
Definition 5.2(v), with the nonarchimedean local-field structure induced by
the spectral norm.  In particular, its value group is identified with
`WithZero (Multiplicative Int)`.  The resulting normalized additive valuation
is compared with both the stage norm and integrality over the base valuation
ring, yielding the effective rational-function monoid used by the local
Frobenioid construction.
-/

open ValuativeRel
open scoped NNReal NormedField WithZero

namespace Iut.SourceFinitePlaceReconstruction

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

noncomputable instance closureIsUltrametricDist
    (place : NumberField.FinitePlace K) :
    IsUltrametricDist (Closure place) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm
      (K := Base place) (L := Closure place))

noncomputable instance stageNontriviallyNormedField
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    NontriviallyNormedField stage where
  toNormedField := inferInstance
  non_trivial := by
    obtain ⟨value, value_norm⟩ :=
      NormedField.exists_one_lt_norm (Base place)
    refine ⟨algebraMap (Base place) stage value, ?_⟩
    change 1 < ‖algebraMap (Base place) (Closure place) value‖
    simpa only [norm_algebraMap'] using value_norm

noncomputable instance stageValuativeRel
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    ValuativeRel stage :=
  ValuativeRel.ofValuation
    (NormedField.valuation : Valuation stage ℝ≥0)

noncomputable instance stageValuationCompatible
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    (NormedField.valuation : Valuation stage ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (NormedField.valuation : Valuation stage ℝ≥0)

noncomputable instance stageIsValuativeTopology
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    IsValuativeTopology stage :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (NormedField.valuation : Valuation stage ℝ≥0) (by
      intro set
      exact @Valued.is_topological_valuation stage inferInstance ℝ≥0
        inferInstance (NormedField.toValued (K := stage)) set)

noncomputable instance stageValuativeNontrivial
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    ValuativeRel.IsNontrivial stage :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (NormedField.valuation : Valuation stage ℝ≥0)).mpr inferInstance

noncomputable instance stageIsNonarchimedeanLocalField
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    IsNonarchimedeanLocalField stage where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

noncomputable def stageValueGroupWithZeroIsoInt
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    ValueGroupWithZero stage ≃*o ℤᵐ⁰ :=
  IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt stage

theorem stageValuativeRel_isDiscrete
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    ValuativeRel.IsDiscrete stage :=
  inferInstance

noncomputable def natGrothendieckToInt :
    Algebra.GrothendieckAddGroup ℕ →+ ℤ :=
  Algebra.GrothendieckAddGroup.lift
    (Int.ofNatHom : ℕ →+ ℤ)

noncomputable def intToNatGrothendieck :
    ℤ →+ Algebra.GrothendieckAddGroup ℕ :=
  zmultiplesHom (Algebra.GrothendieckAddGroup ℕ)
    (Algebra.GrothendieckAddGroup.of 1)

@[simp]
theorem natGrothendieckToInt_of (value : ℕ) :
    natGrothendieckToInt
      (Algebra.GrothendieckAddGroup.of value) = value := by
  have equality :=
    (Algebra.GrothendieckAddGroup.lift
      (M := ℕ) (G := ℤ)).symm_apply_apply
        (Int.ofNatHom : ℕ →+ ℤ)
  exact DFunLike.congr_fun equality value

@[simp]
theorem intToNatGrothendieck_ofNat (value : ℕ) :
    intToNatGrothendieck (value : ℤ) =
      Algebra.GrothendieckAddGroup.of value := by
  change (value : ℤ) • Algebra.GrothendieckAddGroup.of 1 =
    Algebra.GrothendieckAddGroup.of value
  simp [← map_nsmul]

theorem natGrothendieck_right_hom :
    (natGrothendieckToInt.comp intToNatGrothendieck) =
      AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext_int
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  have intToOne :
      intToNatGrothendieck (1 : ℤ) =
        Algebra.GrothendieckAddGroup.of 1 := by
    simpa using intToNatGrothendieck_ofNat 1
  rw [intToOne]
  exact natGrothendieckToInt_of 1

theorem natGrothendieck_left_hom :
    (intToNatGrothendieck.comp natGrothendieckToInt) =
      AddMonoidHom.id (Algebra.GrothendieckAddGroup ℕ) := by
  apply (Algebra.GrothendieckAddGroup.lift
    (M := ℕ) (G := Algebra.GrothendieckAddGroup ℕ)).symm.injective
  apply AddMonoidHom.ext
  intro value
  change intToNatGrothendieck
      (natGrothendieckToInt
        (Algebra.GrothendieckAddGroup.of value)) =
    Algebra.GrothendieckAddGroup.of value
  rw [natGrothendieckToInt_of, intToNatGrothendieck_ofNat]

noncomputable def natGrothendieckEquivInt :
    Algebra.GrothendieckAddGroup ℕ ≃+ ℤ :=
  { toFun := natGrothendieckToInt
    invFun := intToNatGrothendieck
    left_inv := fun value =>
      DFunLike.congr_fun natGrothendieck_left_hom value
    right_inv := fun value =>
      DFunLike.congr_fun natGrothendieck_right_hom value
    map_add' := natGrothendieckToInt.map_add }

@[simp]
theorem natGrothendieckEquivInt_of (value : ℕ) :
    natGrothendieckEquivInt
      (Algebra.GrothendieckAddGroup.of value) = value :=
  natGrothendieckToInt_of value

noncomputable def naturalDivisorialAddMonoid : DivisorialAddMonoid where
  carrier := ℕ
  integral := fun _ _ _ equality => Nat.add_left_cancel equality
  sharp := fun _ hypothesis => Nat.isAddUnit_iff.mp hypothesis
  saturated := by
    intro value multiple hypothesis
    obtain ⟨divisor, equality⟩ := hypothesis
    have mappedEquality := congrArg natGrothendieckEquivInt equality
    have mappedEquality' :
        multiple.1 • natGrothendieckEquivInt value =
          (divisor : ℤ) := by
      simpa only [map_nsmul, natGrothendieckEquivInt_of] using
        mappedEquality.symm
    have valueNonnegative :
        0 ≤ natGrothendieckEquivInt value := by
      apply (nsmul_nonneg_iff (Nat.ne_of_gt multiple.2)).mp
      rw [mappedEquality']
      exact Int.natCast_nonneg divisor
    refine ⟨Int.toNat (natGrothendieckEquivInt value), ?_⟩
    apply natGrothendieckEquivInt.injective
    rw [natGrothendieckEquivInt_of]
    exact Int.toNat_of_nonneg valueNonnegative

noncomputable def stageNormalizedAdditiveValuation
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Additive stageˣ →+ ℤ where
  toFun unit :=
    -WithZero.log
      (stageValueGroupWithZeroIsoInt place stage
        (ValuativeRel.valuation stage unit.toMul.1))
  map_zero' := by
    simp
  map_add' := by
    intro first second
    change
      -WithZero.log
          (stageValueGroupWithZeroIsoInt place stage
            (ValuativeRel.valuation stage
              (first.toMul.1 * second.toMul.1))) =
        -WithZero.log
            (stageValueGroupWithZeroIsoInt place stage
              (ValuativeRel.valuation stage first.toMul.1)) +
          -WithZero.log
            (stageValueGroupWithZeroIsoInt place stage
              (ValuativeRel.valuation stage second.toMul.1))
    rw [map_mul, map_mul, WithZero.log_mul]
    · abel
    · simp
    · simp

theorem stageNormalizedAdditiveValuation_nonnegative_iff
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (unit : stageˣ) :
    0 ≤ stageNormalizedAdditiveValuation place stage
        (Additive.ofMul unit) ↔
      ValuativeRel.valuation stage unit.1 ≤ 1 := by
  let value := ValuativeRel.valuation stage unit.1
  let normalizedValue :=
    stageValueGroupWithZeroIsoInt place stage value
  have normalizedValue_ne_zero : normalizedValue ≠ 0 := by
    simp [normalizedValue, value]
  change 0 ≤ -WithZero.log normalizedValue ↔ value ≤ 1
  rw [neg_nonneg]
  have logComparison :
      WithZero.log normalizedValue ≤ 0 ↔ normalizedValue ≤ 1 := by
    simpa using
      (WithZero.log_le_log normalizedValue_ne_zero one_ne_zero)
  rw [logComparison]
  simpa [normalizedValue] using
    (map_le_map_iff (stageValueGroupWithZeroIsoInt place stage)
      (a := value) (b := 1))

theorem stageNormalizedAdditiveValuation_nonnegative_iff_isIntegral
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (unit : stageˣ) :
    0 ≤ stageNormalizedAdditiveValuation place stage
        (Additive.ofMul unit) ↔
      IsIntegral
        (Valuation.integer (ValuativeRel.valuation stage)) unit.1 :=
  (stageNormalizedAdditiveValuation_nonnegative_iff
      place stage unit).trans
    ((Valuation.integer.integers
      (ValuativeRel.valuation stage)).isIntegral_iff_v_le_one).symm

theorem baseValuation_le_one_iff_norm
    (place : NumberField.FinitePlace K) (value : Base place) :
    ValuativeRel.valuation (Base place) value ≤ 1 ↔ ‖value‖ ≤ 1 := by
  let baseValuation : Valuation (Base place) ℤᵐ⁰ := Valued.v
  letI : baseValuation.Compatible :=
    Valuation.Compatible.ofValuation baseValuation
  refine (ValuativeRel.isEquiv
    baseValuation
    (ValuativeRel.valuation (Base place))).le_one_iff_le_one.symm.trans ?_
  exact (Valued.toNormedField.norm_le_one_iff
    (L := Base place) (Γ₀ := ℤᵐ⁰) (x := value)).symm

theorem stageValuation_le_one_iff_norm
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (value : stage) :
    ValuativeRel.valuation stage value ≤ 1 ↔ ‖value‖ ≤ 1 := by
  refine (ValuativeRel.isEquiv
    (NormedField.valuation : Valuation stage ℝ≥0)
    (ValuativeRel.valuation stage)).le_one_iff_le_one.symm.trans ?_
  change ‖value‖₊ ≤ 1 ↔ ‖value‖ ≤ 1
  exact NNReal.coe_le_coe

theorem stageIsIntegral_iff_norm_le_one
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (value : stage) :
    IsIntegral
        (Valuation.integer (ValuativeRel.valuation (Base place))) value ↔
      ‖value‖ ≤ 1 := by
  let baseIntegers :=
    Valuation.integer (ValuativeRel.valuation (Base place))
  constructor
  · intro integral
    have minpolyEquality :
        minpoly (Base place) value =
          (minpoly baseIntegers value).map
            (algebraMap baseIntegers (Base place)) :=
      minpoly.isIntegrallyClosed_eq_field_fractions'
        (Base place) integral
    rw [NormedAlgebra.norm_eq_spectralNorm (Base place), spectralNorm]
    apply (spectralValue_le_one_iff
      (minpoly.monic
        (Algebra.IsAlgebraic.isAlgebraic value).isIntegral)).mpr
    intro index
    have coefficientEquality :=
      congrArg (fun polynomial => polynomial.coeff index) minpolyEquality
    rw [Polynomial.coeff_map] at coefficientEquality
    calc
      ‖(minpoly (Base place) value).coeff index‖ =
          ‖algebraMap baseIntegers (Base place)
            ((minpoly baseIntegers value).coeff index)‖ :=
        congrArg norm coefficientEquality
      _ ≤ 1 := (baseValuation_le_one_iff_norm place _).mp
        ((minpoly baseIntegers value).coeff index |>.2)
  · intro normLeOne
    have spectralLeOne :
        spectralNorm (Base place) stage value ≤ 1 := by
      calc
        spectralNorm (Base place) stage value = ‖value‖ :=
          (NormedAlgebra.norm_eq_spectralNorm (Base place) value).symm
        _ ≤ 1 := normLeOne
    have coefficientNormLeOne :
        ∀ index : ℕ, ‖(minpoly (Base place) value).coeff index‖ ≤ 1 := by
      apply (spectralValue_le_one_iff
        (minpoly.monic
          (Algebra.IsAlgebraic.isAlgebraic value).isIntegral)).mp
      exact spectralLeOne
    have lifts :
        minpoly (Base place) value ∈
          Polynomial.lifts (algebraMap baseIntegers (Base place)) := by
      apply (Polynomial.lifts_iff_coeff_lifts
        (minpoly (Base place) value)).mpr
      intro index
      let coefficient := (minpoly (Base place) value).coeff index
      have coefficientValuationLeOne :
          ValuativeRel.valuation (Base place) coefficient ≤ 1 :=
        (baseValuation_le_one_iff_norm place coefficient).mpr
          (coefficientNormLeOne index)
      exact ⟨⟨coefficient, coefficientValuationLeOne⟩, rfl⟩
    obtain ⟨polynomial, polynomialMap, _, polynomialMonic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic lifts
        (minpoly.monic
          (Algebra.IsAlgebraic.isAlgebraic value).isIntegral)
    refine ⟨polynomial, polynomialMonic, ?_⟩
    have evaluationEquality :=
      Polynomial.aeval_map_algebraMap (Base place) value polynomial
    rw [polynomialMap, minpoly.aeval] at evaluationEquality
    exact evaluationEquality.symm

theorem stageIsIntegral_closure_iff_valuation_le_one
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (value : stage) :
    IsIntegral
        (Valuation.integer (ValuativeRel.valuation (Base place)))
        (value : Closure place) ↔
      ValuativeRel.valuation stage value ≤ 1 :=
  IntermediateField.coe_isIntegral_iff.trans
    ((stageIsIntegral_iff_norm_le_one place stage value).trans
      (stageValuation_le_one_iff_norm place stage value).symm)

theorem stageNormalizedAdditiveValuation_nonnegative_iff_baseIsIntegral
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (unit : stageˣ) :
    0 ≤ stageNormalizedAdditiveValuation place stage
        (Additive.ofMul unit) ↔
      IsIntegral
        (Valuation.integer (ValuativeRel.valuation (Base place)))
        (unit.1 : Closure place) :=
  (stageNormalizedAdditiveValuation_nonnegative_iff
      place stage unit).trans
    (stageIsIntegral_closure_iff_valuation_le_one
      place stage unit.1).symm

noncomputable def stageEffectiveRationalFunctionSubmonoid
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Submonoid (Multiplicative (Additive stageˣ)) where
  carrier := { value |
    0 ≤ stageNormalizedAdditiveValuation place stage value.toAdd }
  one_mem' := by
    change 0 ≤ stageNormalizedAdditiveValuation place stage 0
    rw [map_zero]
  mul_mem' := by
    intro first second firstEffective secondEffective
    change 0 ≤ stageNormalizedAdditiveValuation place stage
      (first.toAdd + second.toAdd)
    rw [map_add]
    exact add_nonneg firstEffective secondEffective

noncomputable def stageEffectiveRationalFunctionEquivIntegralMonoid
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    stageEffectiveRationalFunctionSubmonoid place stage ≃*
      StageIntegralMonoid place stage where
  toFun value :=
    ⟨value.1.toAdd.toMul.1, by
      constructor
      · exact
          (stageNormalizedAdditiveValuation_nonnegative_iff_baseIsIntegral
            place stage value.1.toAdd.toMul).mp value.2
      · intro closureZero
        apply Units.ne_zero value.1.toAdd.toMul
        apply Subtype.ext
        exact closureZero⟩
  invFun value := by
    have value_ne_zero : value.1 ≠ 0 := by
      intro equality
      apply value.2.2
      rw [equality]
      exact map_zero stage.toIntermediateField.val
    let unit := Units.mk0 value.1 value_ne_zero
    exact
      ⟨Multiplicative.ofAdd (Additive.ofMul unit),
        (stageNormalizedAdditiveValuation_nonnegative_iff_baseIsIntegral
          place stage unit).mpr value.2.1⟩
  left_inv value := by
    apply Subtype.ext
    change
      (Units.mk0 value.1.toAdd.toMul.1
          (Units.ne_zero value.1.toAdd.toMul) : stageˣ) =
        value.1.toAdd.toMul
    exact Units.mk0_val _ _
  right_inv value := by
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply Subtype.ext
    rfl

end

end Iut.SourceFinitePlaceReconstruction
