/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid
import Iut.Foundations.SourceModelFrobenioidZeroEvaluation
import Iut.Foundations.SourceModelFrobenioidIntegralNaturality
import Iut.Foundations.SourceFiniteStageValuationDivisor
import Iut.Foundations.SourceDefinition52IndSystem
import Mathlib.Algebra.Category.MonCat.FilteredColimits

open CategoryTheory CategoryTheory.Limits

/-!
# Finite-stage model evaluation

The explicit model-Frobenioid input at a finite Galois stage has an effective
rational-function submonoid.  Its divisor-effectivity is proved equivalent to
the normalized valuation being nonnegative, and hence to the actual nonzero
integral stage monoid.  This is a finite-stage arithmetic identification; it
does not assert the categorical MLF/CAF realization or an ind-limit theorem.
-/

namespace Iut.SourceFinitePlaceReconstruction

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

theorem stageDivisorGrothendieckEquivInt_intTo
    (exponent : ℤ) :
    stageDivisorGrothendieckEquivInt
        (intToStageDivisorGrothendieck exponent) = exponent := by
  change stageDivisorGrothendieckEquivInt
      ((stageDivisorGrothendieckEquivInt).symm exponent) = exponent
  exact (stageDivisorGrothendieckEquivInt).apply_symm_apply exponent

theorem stageModelEffectiveSubmonoid_eq
    (place : NumberField.FinitePlace K) (stage : StageBase place) :
    SourceModelFrobenioid.Carrier.effectiveRationalFunctionSubmonoid
        (Phi := stageDivisorialMonoidOn place)
        (data := stageModelInput place)
        (SourceModelFrobenioid.Carrier.zeroObject
          (stageDivisorialMonoidOn place) (stageModelInput place) stage) =
      stageEffectiveRationalFunctionSubmonoid place stage.unop := by
  ext value
  constructor
  · rintro ⟨divisor, divisor_eq⟩
    change 0 ≤ stageNormalizedAdditiveValuation place stage.unop value.toAdd
    change Algebra.GrothendieckAddGroup.of divisor = intToStageDivisorGrothendieck
      (stageNormalizedAdditiveValuation place stage.unop value.toAdd) at divisor_eq
    have mapped := congrArg stageDivisorGrothendieckEquivInt divisor_eq
    have value_eq :
        (divisor.down : ℤ) =
          stageNormalizedAdditiveValuation place stage.unop value.toAdd := by
      calc
        (divisor.down : ℤ) =
            stageDivisorGrothendieckEquivInt
              (Algebra.GrothendieckAddGroup.of divisor) := by
          symm
          exact stageDivisorGrothendieckEquivInt_of divisor
        _ = stageDivisorGrothendieckEquivInt
              (intToStageDivisorGrothendieck
                (stageNormalizedAdditiveValuation place stage.unop value.toAdd)) :=
          mapped
        _ = stageNormalizedAdditiveValuation place stage.unop value.toAdd :=
          stageDivisorGrothendieckEquivInt_intTo _
    rw [← value_eq]
    exact Int.natCast_nonneg divisor.down
  · intro value_nonnegative
    change 0 ≤ stageNormalizedAdditiveValuation place stage.unop value.toAdd at value_nonnegative
    refine ⟨ULift.up (Int.toNat
      (stageNormalizedAdditiveValuation place stage.unop value.toAdd)), ?_⟩
    change Algebra.GrothendieckAddGroup.of
        (ULift.up (Int.toNat
          (stageNormalizedAdditiveValuation place stage.unop value.toAdd))) =
      intToStageDivisorGrothendieck
        (stageNormalizedAdditiveValuation place stage.unop value.toAdd)
    apply stageDivisorGrothendieckEquivInt.injective
    rw [stageDivisorGrothendieckEquivInt_of,
      stageDivisorGrothendieckEquivInt_intTo]
    exact Int.toNat_of_nonneg value_nonnegative

noncomputable def stageModelEffectiveRationalFunctionEquivIntegralMonoid
    (place : NumberField.FinitePlace K) (stage : StageBase place) :
    SourceModelFrobenioid.Carrier.effectiveRationalFunctionSubmonoid
        (Phi := stageDivisorialMonoidOn place)
        (data := stageModelInput place)
        (SourceModelFrobenioid.Carrier.zeroObject
          (stageDivisorialMonoidOn place) (stageModelInput place) stage) ≃*
      StageIntegralMonoid place stage.unop where
  toFun value :=
    ⟨value.1.toAdd.toMul.1, by
      have value_nonnegative :
          value.1 ∈ stageEffectiveRationalFunctionSubmonoid
            place stage.unop := by
        rw [← stageModelEffectiveSubmonoid_eq place stage]
        exact value.2
      constructor
      · exact
          (stageNormalizedAdditiveValuation_nonnegative_iff_baseIsIntegral
            place stage.unop value.1.toAdd.toMul).mp value_nonnegative
      · intro closureZero
        apply Units.ne_zero value.1.toAdd.toMul
        apply Subtype.ext
        exact closureZero⟩
  invFun value := by
    have value_ne_zero : value.1 ≠ 0 := by
      intro equality
      apply value.2.2
      rw [equality]
      exact map_zero stage.unop.toIntermediateField.val
    let unit := Units.mk0 value.1 value_ne_zero
    have effectiveValue :
        Multiplicative.ofAdd (Additive.ofMul unit) ∈
          SourceModelFrobenioid.Carrier.effectiveRationalFunctionSubmonoid
            (Phi := stageDivisorialMonoidOn place)
            (data := stageModelInput place)
            (SourceModelFrobenioid.Carrier.zeroObject
              (stageDivisorialMonoidOn place) (stageModelInput place) stage) := by
      rw [stageModelEffectiveSubmonoid_eq]
      exact
        (stageNormalizedAdditiveValuation_nonnegative_iff_baseIsIntegral
          place stage.unop unit).mpr value.2.1
    exact ⟨Multiplicative.ofAdd (Additive.ofMul unit), effectiveValue⟩
  left_inv value := by
    apply Subtype.ext
    change
      (Units.mk0 value.1.toAdd.toMul.1
          (Units.ne_zero value.1.toAdd.toMul) : stage.unopˣ) =
        value.1.toAdd.toMul
    exact Units.mk0_val _ _
  right_inv value := by
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply Subtype.ext
    rfl

noncomputable def stageModelZeroObjectRationalFunctionEquivIntegralMonoid
    (place : NumberField.FinitePlace K) (stage : StageBase place) :
    (_root_.Iut.SourceModelFrobenioid.Carrier.preFrobenioid
      (Phi := stageDivisorialMonoidOn place)
      (data := stageModelInput place)).LinearBaseIdentityEndomorphism
        (SourceModelFrobenioid.Carrier.zeroObject
          (stageDivisorialMonoidOn place) (stageModelInput place) stage) ≃*
      StageIntegralMonoid place stage.unop :=
    (SourceModelFrobenioid.Carrier.zeroObjectRationalFunctionEquiv
      (Phi := stageDivisorialMonoidOn place)
      (data := stageModelInput place) stage).trans
    (stageModelEffectiveRationalFunctionEquivIntegralMonoid place stage)

theorem stageModelEffectiveRationalFunctionEquivIntegralMonoid_natural
    (place : NumberField.FinitePlace K)
    {source target : StageBase place} (arrow : source ⟶ target) :
    (stageModelEffectiveRationalFunctionEquivIntegralMonoid place source).toMonoidHom.comp
        (SourceModelFrobenioid.Carrier.effectiveRationalFunctionPullback
          (Phi := stageDivisorialMonoidOn place)
          (data := stageModelInput place) arrow) =
      (stageIntegralTransition place arrow.unop.le).hom.comp
        (stageModelEffectiveRationalFunctionEquivIntegralMonoid place target).toMonoidHom := by
  apply MonoidHom.ext
  intro value
  apply Subtype.ext
  simp [stageModelEffectiveRationalFunctionEquivIntegralMonoid,
    SourceModelFrobenioid.Carrier.effectiveRationalFunctionPullback,
    stageIntegralTransition, stageModelInput, stageRationalFunctions,
    stageUnitTransition, transitionContinuousLinearMap, transitionLinearMap]
  dsimp [stageModelEffectiveRationalFunctionEquivIntegralMonoid,
    MonoidHom.comp]
  rfl

def stageIntegralMonoidFunctor
    (place : NumberField.FinitePlace K) :
    (StageBase place)ᵒᵖ ⥤ MonCat.{u} where
  obj stage := MonCat.of (StageIntegralMonoid place stage.unop.unop)
  map arrow := MonCat.ofHom
    (stageIntegralTransition place arrow.unop.unop.le).hom
  map_id stage := by
    apply MonCat.hom_ext
    exact congrArg ContinuousMonoidHom.hom
      (stageIntegralTransition_refl place stage.unop.unop)
  map_comp first second := by
    apply MonCat.hom_ext
    exact congrArg ContinuousMonoidHom.hom
      (stageIntegralTransition_trans place
        first.unop.unop.le second.unop.unop.le)

def stageModelEffectiveToIntegralNatIso
    (place : NumberField.FinitePlace K) :
    SourceModelFrobenioid.Carrier.effectiveRationalFunctionFunctor
        (Phi := stageDivisorialMonoidOn place)
        (data := stageModelInput place) ≅
      stageIntegralMonoidFunctor place :=
  NatIso.ofComponents
    (fun stage =>
      { hom := MonCat.ofHom
          (stageModelEffectiveRationalFunctionEquivIntegralMonoid
            place stage.unop).toMonoidHom
        inv := MonCat.ofHom
          (stageModelEffectiveRationalFunctionEquivIntegralMonoid
            place stage.unop).symm.toMonoidHom
        hom_inv_id := by
          apply MonCat.hom_ext
          apply MonoidHom.ext
          intro value
          exact (stageModelEffectiveRationalFunctionEquivIntegralMonoid
            place stage.unop).symm_apply_apply value
        inv_hom_id := by
          apply MonCat.hom_ext
          apply MonoidHom.ext
          intro value
          exact (stageModelEffectiveRationalFunctionEquivIntegralMonoid
            place stage.unop).apply_symm_apply value })
    (fun {source target} arrow => by
      apply MonCat.hom_ext
      exact stageModelEffectiveRationalFunctionEquivIntegralMonoid_natural
        place arrow.unop)

def stageModelZeroObjectToIntegralNatIso
    (place : NumberField.FinitePlace K) :
    SourceModelFrobenioid.Carrier.zeroRationalMonoidFunctor
        (Phi := stageDivisorialMonoidOn place)
        (data := stageModelInput place) ≅
      stageIntegralMonoidFunctor place :=
  (SourceModelFrobenioid.Carrier.zeroRationalFunctionNatIso
      (Phi := stageDivisorialMonoidOn place)
      (data := stageModelInput place)).trans
    (stageModelEffectiveToIntegralNatIso place)

abbrev stageIntegralFilteredFunctor
    (place : NumberField.FinitePlace K) :=
  stageIntegralMonoidFunctor place

def stageIntegralToIndCocone
    (place : NumberField.FinitePlace K) :
    Cocone (stageIntegralFilteredFunctor place) where
  pt := MonCat.of (IndIntegralMonoid place)
  ι := {
    app := fun stage =>
      MonCat.ofHom (stageIntegralToIndHom place stage.unop.unop)
    naturality := by
      intro first second arrow
      apply MonCat.hom_ext
      exact stageIntegralToIndHom_transition place arrow.unop.unop.le }

noncomputable abbrev stageIntegralFilteredColimit
    (place : NumberField.FinitePlace K) : MonCat.{u} :=
  MonCat.FilteredColimits.colimit (stageIntegralFilteredFunctor place)

noncomputable def stageIntegralFilteredColimitToInd
    (place : NumberField.FinitePlace K) :
    stageIntegralFilteredColimit place ⟶ MonCat.of (IndIntegralMonoid place) :=
  MonCat.FilteredColimits.colimitDesc
    (stageIntegralFilteredFunctor place) (stageIntegralToIndCocone place)

theorem stageIntegralFilteredColimitToInd_cocone
    (place : NumberField.FinitePlace K)
    (stage : (StageBase place)ᵒᵖ) :
    (MonCat.FilteredColimits.coconeMorphism
      (stageIntegralFilteredFunctor place) stage) ≫
        stageIntegralFilteredColimitToInd place =
      (stageIntegralToIndCocone place).ι.app stage := by
  exact (MonCat.FilteredColimits.colimitCoconeIsColimit
    (stageIntegralFilteredFunctor place)).fac
    (stageIntegralToIndCocone place) stage

theorem stageIntegralFilteredColimitToInd_surjective
    (place : NumberField.FinitePlace K) :
    Function.Surjective (stageIntegralFilteredColimitToInd place) := by
  intro value
  obtain ⟨stage, stageValue, value_eq⟩ :=
    exists_stage_representation place value
  let index : (StageBase place)ᵒᵖ := Opposite.op (Opposite.op stage)
  let represented : stageIntegralFilteredColimit place :=
    MonCat.FilteredColimits.coconeMorphism
      (stageIntegralFilteredFunctor place) index stageValue
  refine ⟨represented, ?_⟩
  change stageIntegralToIndHom place stage stageValue = value
  exact value_eq

theorem stageIntegralFilteredColimitToInd_injective
    (place : NumberField.FinitePlace K) :
    Function.Injective (stageIntegralFilteredColimitToInd place) := by
  intro first second equality
  obtain ⟨firstStage, firstValue, first_eq⟩ :=
    MonCat.FilteredColimits.M.mk_surjective
      (stageIntegralFilteredFunctor place) first
  obtain ⟨secondStage, secondValue, second_eq⟩ :=
    MonCat.FilteredColimits.M.mk_surjective
      (stageIntegralFilteredFunctor place) second
  have first_image :
      stageIntegralFilteredColimitToInd place
          (MonCat.FilteredColimits.M.mk
            (stageIntegralFilteredFunctor place) ⟨firstStage, firstValue⟩) =
        stageIntegralToIndHom place firstStage.unop.unop firstValue := by
    have factor := congrArg (fun f => f firstValue)
      (stageIntegralFilteredColimitToInd_cocone place firstStage)
    exact factor
  have second_image :
      stageIntegralFilteredColimitToInd place
          (MonCat.FilteredColimits.M.mk
            (stageIntegralFilteredFunctor place) ⟨secondStage, secondValue⟩) =
        stageIntegralToIndHom place secondStage.unop.unop secondValue := by
    have factor := congrArg (fun f => f secondValue)
      (stageIntegralFilteredColimitToInd_cocone place secondStage)
    exact factor
  have representative_image_eq :
      stageIntegralFilteredColimitToInd place
          (MonCat.FilteredColimits.M.mk
            (stageIntegralFilteredFunctor place) ⟨firstStage, firstValue⟩) =
        stageIntegralFilteredColimitToInd place
          (MonCat.FilteredColimits.M.mk
            (stageIntegralFilteredFunctor place) ⟨secondStage, secondValue⟩) := by
    calc
      _ = stageIntegralFilteredColimitToInd place first :=
        congrArg (stageIntegralFilteredColimitToInd place) first_eq
      _ = stageIntegralFilteredColimitToInd place second := equality
      _ = _ := congrArg (stageIntegralFilteredColimitToInd place) second_eq.symm
  have image_eq :
      stageIntegralToIndHom place firstStage.unop.unop firstValue =
        stageIntegralToIndHom place secondStage.unop.unop secondValue := by
    rw [← first_image, ← second_image]
    exact representative_image_eq
  let common := IsFiltered.max firstStage secondStage
  let firstToCommon := IsFiltered.leftToMax firstStage secondStage
  let secondToCommon := IsFiltered.rightToMax firstStage secondStage
  have common_image_eq :
      stageIntegralToIndHom place common.unop.unop
          ((stageIntegralFilteredFunctor place).map firstToCommon firstValue) =
        stageIntegralToIndHom place common.unop.unop
          ((stageIntegralFilteredFunctor place).map secondToCommon secondValue) := by
    calc
      stageIntegralToIndHom place common.unop.unop
          ((stageIntegralFilteredFunctor place).map firstToCommon firstValue) =
          stageIntegralToIndHom place firstStage.unop.unop firstValue := by
            change
              (stageIntegralToIndHom place common.unop.unop).comp
                  (stageIntegralTransition place firstToCommon.unop.unop.le).hom firstValue = _
            rw [stageIntegralToIndHom_transition]
            rfl
      _ = stageIntegralToIndHom place secondStage.unop.unop secondValue := image_eq
      _ = stageIntegralToIndHom place common.unop.unop
          ((stageIntegralFilteredFunctor place).map secondToCommon secondValue) := by
            change _ =
              (stageIntegralToIndHom place common.unop.unop).comp
                (stageIntegralTransition place secondToCommon.unop.unop.le).hom secondValue
            rw [stageIntegralToIndHom_transition]
            rfl
  have common_value_eq :
      (stageIntegralFilteredFunctor place).map firstToCommon firstValue =
        (stageIntegralFilteredFunctor place).map secondToCommon secondValue :=
    stageIntegralToIndHom_injective place common.unop.unop common_image_eq
  have representative_eq :=
    MonCat.FilteredColimits.M.mk_eq
      (stageIntegralFilteredFunctor place)
      ⟨firstStage, firstValue⟩ ⟨secondStage, secondValue⟩
      ⟨common, firstToCommon, secondToCommon, common_value_eq⟩
  exact first_eq.symm.trans (representative_eq.trans second_eq)

noncomputable def stageIntegralFilteredColimitEquivInd
    (place : NumberField.FinitePlace K) :
    (stageIntegralFilteredColimit place).carrier ≃*
      IndIntegralMonoid place :=
  MulEquiv.ofBijective
    (stageIntegralFilteredColimitToInd place).hom
    ⟨stageIntegralFilteredColimitToInd_injective place,
      stageIntegralFilteredColimitToInd_surjective place⟩

abbrev stageModelZeroObjectFilteredFunctor
    (place : NumberField.FinitePlace K) :=
  SourceModelFrobenioid.Carrier.zeroRationalMonoidFunctor
    (Phi := stageDivisorialMonoidOn place)
    (data := stageModelInput place)

noncomputable abbrev stageModelZeroObjectFilteredColimit
    (place : NumberField.FinitePlace K) : MonCat.{u} :=
  MonCat.FilteredColimits.colimit
    (stageModelZeroObjectFilteredFunctor place)

def stageModelZeroObjectToIntegralCocone
    (place : NumberField.FinitePlace K) :
    Cocone (stageModelZeroObjectFilteredFunctor place) where
  pt := stageIntegralFilteredColimit place
  ι := {
    app := fun stage =>
      (stageModelZeroObjectToIntegralNatIso place).hom.app stage ≫
        MonCat.FilteredColimits.coconeMorphism
          (stageIntegralFilteredFunctor place) stage
    naturality := by
      intro source target arrow
      change
        (stageModelZeroObjectFilteredFunctor place).map arrow ≫
            (stageModelZeroObjectToIntegralNatIso place).hom.app target ≫
          MonCat.FilteredColimits.coconeMorphism
            (stageIntegralFilteredFunctor place) target =
        (stageModelZeroObjectToIntegralNatIso place).hom.app source ≫
          MonCat.FilteredColimits.coconeMorphism
            (stageIntegralFilteredFunctor place) source
      rw [← Category.assoc,
        (stageModelZeroObjectToIntegralNatIso place).hom.naturality]
      rw [Category.assoc, MonCat.FilteredColimits.cocone_naturality]
  }

noncomputable def stageModelZeroObjectFilteredColimitToIntegral
    (place : NumberField.FinitePlace K) :
    stageModelZeroObjectFilteredColimit place ⟶
      stageIntegralFilteredColimit place :=
  MonCat.FilteredColimits.colimitDesc
    (stageModelZeroObjectFilteredFunctor place)
    (stageModelZeroObjectToIntegralCocone place)

theorem stageModelZeroObjectFilteredColimitToIntegral_cocone
    (place : NumberField.FinitePlace K)
    (stage : (StageBase place)ᵒᵖ) :
    (MonCat.FilteredColimits.coconeMorphism
      (stageModelZeroObjectFilteredFunctor place) stage) ≫
        stageModelZeroObjectFilteredColimitToIntegral place =
      (stageModelZeroObjectToIntegralNatIso place).hom.app stage ≫
        MonCat.FilteredColimits.coconeMorphism
          (stageIntegralFilteredFunctor place) stage := by
  change
    (MonCat.FilteredColimits.coconeMorphism
      (stageModelZeroObjectFilteredFunctor place) stage) ≫
        stageModelZeroObjectFilteredColimitToIntegral place =
      (stageModelZeroObjectToIntegralCocone place).ι.app stage
  exact (MonCat.FilteredColimits.colimitCoconeIsColimit
    (stageModelZeroObjectFilteredFunctor place)).fac
    (stageModelZeroObjectToIntegralCocone place) stage

def stageIntegralToModelZeroObjectCocone
    (place : NumberField.FinitePlace K) :
    Cocone (stageIntegralFilteredFunctor place) where
  pt := stageModelZeroObjectFilteredColimit place
  ι := {
    app := fun stage =>
      (stageModelZeroObjectToIntegralNatIso place).inv.app stage ≫
        MonCat.FilteredColimits.coconeMorphism
          (stageModelZeroObjectFilteredFunctor place) stage
    naturality := by
      intro source target arrow
      change
        (stageIntegralFilteredFunctor place).map arrow ≫
            (stageModelZeroObjectToIntegralNatIso place).inv.app target ≫
          MonCat.FilteredColimits.coconeMorphism
            (stageModelZeroObjectFilteredFunctor place) target =
        (stageModelZeroObjectToIntegralNatIso place).inv.app source ≫
          MonCat.FilteredColimits.coconeMorphism
            (stageModelZeroObjectFilteredFunctor place) source
      rw [← Category.assoc,
        (stageModelZeroObjectToIntegralNatIso place).inv.naturality]
      rw [Category.assoc, MonCat.FilteredColimits.cocone_naturality]
  }

noncomputable def stageIntegralFilteredColimitToModelZeroObject
    (place : NumberField.FinitePlace K) :
    stageIntegralFilteredColimit place ⟶
      stageModelZeroObjectFilteredColimit place :=
  MonCat.FilteredColimits.colimitDesc
    (stageIntegralFilteredFunctor place)
    (stageIntegralToModelZeroObjectCocone place)

theorem stageIntegralFilteredColimitToModelZeroObject_cocone
    (place : NumberField.FinitePlace K)
    (stage : (StageBase place)ᵒᵖ) :
    (MonCat.FilteredColimits.coconeMorphism
      (stageIntegralFilteredFunctor place) stage) ≫
        stageIntegralFilteredColimitToModelZeroObject place =
      (stageModelZeroObjectToIntegralNatIso place).inv.app stage ≫
        MonCat.FilteredColimits.coconeMorphism
          (stageModelZeroObjectFilteredFunctor place) stage := by
  change
    (MonCat.FilteredColimits.coconeMorphism
      (stageIntegralFilteredFunctor place) stage) ≫
        stageIntegralFilteredColimitToModelZeroObject place =
      (stageIntegralToModelZeroObjectCocone place).ι.app stage
  exact (MonCat.FilteredColimits.colimitCoconeIsColimit
    (stageIntegralFilteredFunctor place)).fac
    (stageIntegralToModelZeroObjectCocone place) stage

noncomputable def stageModelZeroObjectFilteredColimitIsoIntegral
    (place : NumberField.FinitePlace K) :
    stageModelZeroObjectFilteredColimit place ≅
      stageIntegralFilteredColimit place where
  hom := stageModelZeroObjectFilteredColimitToIntegral place
  inv := stageIntegralFilteredColimitToModelZeroObject place
  hom_inv_id := by
    apply (MonCat.FilteredColimits.colimitCoconeIsColimit
      (stageModelZeroObjectFilteredFunctor place)).hom_ext
    intro stage
    change
      ((MonCat.FilteredColimits.coconeMorphism
        (stageModelZeroObjectFilteredFunctor place) stage ≫
          stageModelZeroObjectFilteredColimitToIntegral place) ≫
        stageIntegralFilteredColimitToModelZeroObject place) =
        MonCat.FilteredColimits.coconeMorphism
          (stageModelZeroObjectFilteredFunctor place) stage ≫
          𝟙 (stageModelZeroObjectFilteredColimit place)
    rw [stageModelZeroObjectFilteredColimitToIntegral_cocone,
      Category.assoc,
      stageIntegralFilteredColimitToModelZeroObject_cocone]
    simp
  inv_hom_id := by
    apply (MonCat.FilteredColimits.colimitCoconeIsColimit
      (stageIntegralFilteredFunctor place)).hom_ext
    intro stage
    change
      ((MonCat.FilteredColimits.coconeMorphism
        (stageIntegralFilteredFunctor place) stage ≫
          stageIntegralFilteredColimitToModelZeroObject place) ≫
        stageModelZeroObjectFilteredColimitToIntegral place) =
        MonCat.FilteredColimits.coconeMorphism
          (stageIntegralFilteredFunctor place) stage ≫
          𝟙 (stageIntegralFilteredColimit place)
    rw [stageIntegralFilteredColimitToModelZeroObject_cocone,
      Category.assoc,
      stageModelZeroObjectFilteredColimitToIntegral_cocone]
    simp

noncomputable def stageModelZeroObjectFilteredColimitEquivInd
    (place : NumberField.FinitePlace K) :
    (stageModelZeroObjectFilteredColimit place).carrier ≃*
      IndIntegralMonoid place :=
  (CategoryTheory.Iso.monCatIsoToMulEquiv
      (stageModelZeroObjectFilteredColimitIsoIntegral place)).trans
    (stageIntegralFilteredColimitEquivInd place)

noncomputable def stageModelZeroObjectFilteredColimitEquivSourceMLF
    (place : NumberField.FinitePlace K) :
    (stageModelZeroObjectFilteredColimit place).carrier ≃*
      SourceMLFIntegralMonoid (SourceFinitePlaceReconstruction.Base place) :=
  (stageModelZeroObjectFilteredColimitEquivInd place).trans
    (indIntegralMonoidEquivSourceMLF place)

end

end Iut.SourceFinitePlaceReconstruction
