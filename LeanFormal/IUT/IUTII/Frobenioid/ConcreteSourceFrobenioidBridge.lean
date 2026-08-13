import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaCStage
import Iut.Foundations.SourceFiniteStageModelEvaluation
import Iut.Foundations.SourceFiniteStageModelFrobenioid
import Iut.Foundations.SourceFrobenioidUniversalProEvaluation

open CategoryTheory
open CategoryTheory.Limits
open Iut
open Iut.SourceFinitePlaceReconstruction

namespace LeanFormal.IUT

noncomputable section

local instance gaussianPolynomialIrreducibleFactConcreteSource :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactConcreteSource : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactForConcreteSource (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) :=
  l.factPrime

namespace ConcreteSourceFrobenioidBridge

abbrev concretePlace : NumberField.FinitePlace GaussianField :=
  concreteGaussianFivePlace

abbrev concreteStageIndex :=
  Iut.SourceFinitePlaceReconstruction.StageIndex concretePlace

abbrev concreteStageBase :=
  Iut.SourceFinitePlaceReconstruction.StageBase concretePlace

abbrev concreteStageDivisor :=
  Iut.SourceFinitePlaceReconstruction.StageDivisor

abbrev concreteStageModelInput :=
  Iut.SourceFinitePlaceReconstruction.stageModelInput concretePlace

abbrev concreteStageModelDivisorialMonoid :=
  Iut.SourceFinitePlaceReconstruction.stageDivisorialMonoidOn concretePlace

abbrev concreteStageModel :=
  Iut.SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation concretePlace

abbrev concreteStageIntegralFunctor :=
  Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredFunctor concretePlace

abbrev concreteStageIntegralColimit :=
  Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimit concretePlace

abbrev concreteStageZeroFunctor :=
  Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredFunctor concretePlace

abbrev concreteStageZeroColimit :=
  Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimit concretePlace

abbrev concreteStageIndIntegralMonoid :=
  Iut.SourceFinitePlaceReconstruction.IndIntegralMonoid concretePlace

abbrev concreteStageSourceMLF :=
  Iut.SourceMLFIntegralMonoid
    (Iut.SourceFinitePlaceReconstruction.Base concretePlace)

structure ConcreteSourceFrobenioidBoundary (l : PrimeGeFive) where
  cStage : ConcreteInitialThetaCStage l
  place : NumberField.FinitePlace GaussianField
  place_eq : place = concretePlace
  model : Iut.FrobenioidPresentation
  model_eq : model = concreteStageModel
  model_input :
    Iut.SourceModelFrobenioid.Input concreteStageModelDivisorialMonoid
  model_input_eq : model_input = concreteStageModelInput
  local_kernel :
    cStage.localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ)

noncomputable def concreteSourceFrobenioidBoundary (l : PrimeGeFive) :
    ConcreteSourceFrobenioidBoundary l where
  cStage := concreteInitialThetaCStage l
  place := concretePlace
  place_eq := rfl
  model := concreteStageModel
  model_eq := rfl
  model_input := concreteStageModelInput
  model_input_eq := rfl
  local_kernel := concreteInitialThetaCStage_local_finite_kernel l

@[simp] theorem boundary_cStage (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).cStage =
      concreteInitialThetaCStage l :=
  rfl

@[simp] theorem boundary_place (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).place = concretePlace :=
  (concreteSourceFrobenioidBoundary l).place_eq

@[simp] theorem boundary_model (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).model = concreteStageModel :=
  (concreteSourceFrobenioidBoundary l).model_eq

@[simp] theorem boundary_model_input (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).model_input =
      concreteStageModelInput :=
  (concreteSourceFrobenioidBoundary l).model_input_eq

theorem boundary_kernel (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).cStage.localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) :=
  (concreteSourceFrobenioidBoundary l).local_kernel

theorem concrete_place_comap :
    NumberFieldFinitePlace.comap (k := ℚ) concretePlace = concreteFivePlace := by
  exact concreteGaussianFivePlace_comap

theorem concrete_place_stable (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).curve.HasStableReductionAt
      (concreteInitialThetaCStage l).place :=
  concreteInitialThetaCStage_stable l

theorem concrete_place_multiplicative (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).curve.HasMultiplicativeReductionAt
      (concreteInitialThetaCStage l).place :=
  concreteInitialThetaCStage_multiplicative l

theorem concrete_place_selected_input (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).input.place = concretePlace := by
  exact concreteInitialThetaCStage_place l

theorem concrete_place_input_arithmetic (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).input.arithmetic =
      concreteGaussianInitialThetaArithmeticData l := by
  rfl

theorem source_stage_base_connected :
    CategoryTheory.IsConnected concreteStageBase := by
  exact Iut.SourceFinitePlaceReconstruction.stageBase_isConnected concretePlace

noncomputable instance source_stage_base_connected_inst :
    CategoryTheory.IsConnected concreteStageBase :=
  source_stage_base_connected

theorem source_stage_base_is_filtered :
    IsFiltered concreteStageBase := by
  infer_instance

theorem source_stage_base_has_terminal :
    Nonempty (IsTerminal (Opposite.op (⊥ : concreteStageIndex))) := by
  exact ⟨Iut.SourceFinitePlaceReconstruction.stageBaseTerminal concretePlace⟩

theorem source_stage_arrow_epi
    {source target : concreteStageBase} (arrow : source ⟶ target) :
    Epi arrow := by
  exact Iut.SourceFinitePlaceReconstruction.stageBase_arrow_epi concretePlace arrow

theorem source_stage_eq_of_iso
    {source target : concreteStageBase} (arrow : source ⟶ target)
    [IsIso arrow] : source = target := by
  exact Iut.SourceFinitePlaceReconstruction.stageBase_eq_of_isIso arrow

theorem source_stage_divisor_equiv_apply
    (value : concreteStageDivisor) :
    Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt
        (Algebra.GrothendieckAddGroup.of value) =
      value.down := by
  exact Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt_of value

theorem source_stage_divisor_equiv_up
    (value : ℕ) :
    Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt
        (Iut.SourceFinitePlaceReconstruction.intToStageDivisorGrothendieck
          (value : ℤ)) = value := by
  exact Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt_intTo
    (value : ℤ)

theorem source_stage_divisor_to_int_right_inverse :
    Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckToInt.comp
        Iut.SourceFinitePlaceReconstruction.intToStageDivisorGrothendieck =
      AddMonoidHom.id ℤ := by
  exact Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieck_right_hom

theorem source_stage_divisor_to_int_left_inverse :
    Iut.SourceFinitePlaceReconstruction.intToStageDivisorGrothendieck.comp
        Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckToInt =
      AddMonoidHom.id
        (Algebra.GrothendieckAddGroup concreteStageDivisor) := by
  exact Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieck_left_hom

theorem source_stage_divisor_equiv_bijective :
    Function.Bijective
      Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt := by
  exact (Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt).bijective

theorem source_stage_divisor_equiv_injective :
    Function.Injective
      Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt := by
  exact (Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt).injective

theorem source_stage_divisor_equiv_surjective :
    Function.Surjective
      Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt := by
  exact (Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt).surjective

theorem source_stage_divisor_nsmul_up (value : ℕ) :
    value • (ULift.up 1 : concreteStageDivisor) = ULift.up value := by
  exact Iut.SourceFinitePlaceReconstruction.stageDivisor_nsmul_up value

theorem source_stage_divisor_pullback_refl (stage : concreteStageIndex) :
    Iut.SourceFinitePlaceReconstruction.liftedStageDivisorPullback concretePlace
        (show stage ≤ stage from le_rfl) =
      AddMonoidHom.id concreteStageDivisor := by
  exact Iut.SourceFinitePlaceReconstruction.liftedStageDivisorPullback_refl
    concretePlace stage

theorem source_stage_divisor_pullback_trans
    {first second third : concreteStageIndex}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    Iut.SourceFinitePlaceReconstruction.liftedStageDivisorPullback concretePlace
        (firstSecond.trans secondThird) =
      (Iut.SourceFinitePlaceReconstruction.liftedStageDivisorPullback concretePlace
        secondThird).comp
        (Iut.SourceFinitePlaceReconstruction.liftedStageDivisorPullback concretePlace
          firstSecond) := by
  exact Iut.SourceFinitePlaceReconstruction.liftedStageDivisorPullback_trans
    concretePlace firstSecond secondThird

theorem source_stage_divisor_pullback_injective
    {source target : concreteStageIndex} (map : source ≤ target) :
    Function.Injective
      (Iut.SourceFinitePlaceReconstruction.liftedStageDivisorPullback concretePlace map) := by
  exact Iut.SourceFinitePlaceReconstruction.liftedStageDivisorPullback_injective
    concretePlace map

theorem source_stage_divisorial_monoid_pullback_id
    (stage : concreteStageBase) :
    (concreteStageModelDivisorialMonoid).pullback (𝟙 stage) =
      AddMonoidHom.id concreteStageDivisor := by
  exact concreteStageModelDivisorialMonoid.pullback_id stage

theorem source_stage_divisorial_monoid_pullback_comp
    {first middle last : concreteStageBase}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    (concreteStageModelDivisorialMonoid).pullback (f ≫ g) =
      (concreteStageModelDivisorialMonoid.pullback f).comp
        (concreteStageModelDivisorialMonoid.pullback g) := by
  exact concreteStageModelDivisorialMonoid.pullback_comp f g

theorem source_stage_divisorial_monoid_pullback_injective
    {source target : concreteStageBase} (arrow : source ⟶ target) :
    Function.Injective
      (concreteStageModelDivisorialMonoid.pullback arrow) := by
  exact concreteStageModelDivisorialMonoid.characteristicallyInjective arrow

theorem source_stage_divisorial_monoid_obj
    (stage : concreteStageBase) :
    (concreteStageModelDivisorialMonoid).obj stage =
      Iut.SourceFinitePlaceReconstruction.stageDivisorialAddMonoid := by
  rfl

theorem source_stage_rational_functions_obj
    (stage : concreteStageBase) :
    (Iut.SourceFinitePlaceReconstruction.stageRationalFunctions concretePlace).obj stage =
      Additive stage.unopˣ := by
  rfl

theorem source_stage_unit_transition_refl (stage : concreteStageIndex) :
    Iut.SourceFinitePlaceReconstruction.stageUnitTransition concretePlace
        (show stage ≤ stage from le_rfl) =
      MonoidHom.id stageˣ := by
  exact Iut.SourceFinitePlaceReconstruction.stageUnitTransition_refl concretePlace stage

theorem source_stage_unit_transition_trans
    {first second third : concreteStageIndex}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    Iut.SourceFinitePlaceReconstruction.stageUnitTransition concretePlace
        (firstSecond.trans secondThird) =
      (Iut.SourceFinitePlaceReconstruction.stageUnitTransition concretePlace
        secondThird).comp
        (Iut.SourceFinitePlaceReconstruction.stageUnitTransition concretePlace
          firstSecond) := by
  exact Iut.SourceFinitePlaceReconstruction.stageUnitTransition_trans
    concretePlace firstSecond secondThird

theorem source_stage_unit_transition_injective
    {source target : concreteStageIndex} (map : source ≤ target) :
    Function.Injective
      (Iut.SourceFinitePlaceReconstruction.stageUnitTransition concretePlace map) := by
  exact Iut.SourceFinitePlaceReconstruction.stageUnitTransition_injective concretePlace map

theorem source_stage_normalized_valuation_transition
    {source target : concreteStageIndex} (map : source ≤ target)
    (value : sourceˣ) :
    Iut.SourceFinitePlaceReconstruction.stageNormalizedAdditiveValuation concretePlace
        target
        (Additive.ofMul
          (Iut.SourceFinitePlaceReconstruction.stageUnitTransition concretePlace map
            value)) =
      (Iut.SourceFinitePlaceReconstruction.stageNormalizedAdditiveTransition
        concretePlace map
        (Iut.SourceFinitePlaceReconstruction.stageNormalizedAdditiveValuation
          concretePlace source (Additive.ofMul value))) := by
  exact Iut.SourceFinitePlaceReconstruction.stageNormalizedAdditiveValuation_transition
    concretePlace map value

theorem source_stage_divisor_pullback_apply
    {source target : concreteStageBase} (arrow : source ⟶ target)
    (exponent : ℤ) :
    (concreteStageModelDivisorialMonoid).gpPullback arrow
        (Iut.SourceFinitePlaceReconstruction.intToStageDivisorGrothendieck exponent) =
      Iut.SourceFinitePlaceReconstruction.intToStageDivisorGrothendieck
        (Iut.SourceFinitePlaceReconstruction.stageNormalizedAdditiveTransition
          concretePlace arrow.unop.le exponent) := by
  exact Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckPullback_apply
    concretePlace arrow exponent

theorem source_stage_model_divisor_natural
    {source target : concreteStageBase} (arrow : source ⟶ target)
     (value :
       (Iut.SourceFinitePlaceReconstruction.stageRationalFunctions concretePlace).obj target) :
    concreteStageModelInput.divisor source
        (concreteStageModelInput.rationalFunctions.pullback arrow value) =
      (concreteStageModelDivisorialMonoid).gpPullback arrow
        (concreteStageModelInput.divisor target value) := by
  exact concreteStageModelInput.divisor_natural arrow value

theorem source_stage_model_input_rational_pullback_id (stage : concreteStageBase) :
    concreteStageModelInput.rationalFunctions.pullback (𝟙 stage) =
      AddMonoidHom.id _ := by
  exact concreteStageModelInput.rationalFunctions.pullback_id stage

theorem source_stage_model_input_rational_pullback_comp
    {first middle last : concreteStageBase}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    concreteStageModelInput.rationalFunctions.pullback (f ≫ g) =
      (concreteStageModelInput.rationalFunctions.pullback f).comp
        (concreteStageModelInput.rationalFunctions.pullback g) := by
  exact concreteStageModelInput.rationalFunctions.pullback_comp f g

theorem source_stage_model_input_divisor_apply
    (stage : concreteStageBase) (value : Additive stage.unopˣ) :
    concreteStageModelInput.divisor stage value =
      Iut.SourceFinitePlaceReconstruction.intToStageDivisorGrothendieck
        (Iut.SourceFinitePlaceReconstruction.stageNormalizedAdditiveValuation
          concretePlace stage.unop value) := by
  rfl

theorem source_stage_effective_equiv_bijective
    (stage : concreteStageBase) :
    Function.Bijective
      (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveRationalFunctionEquivIntegralMonoid
        concretePlace stage) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveRationalFunctionEquivIntegralMonoid
    concretePlace stage).bijective

theorem source_stage_effective_submonoid_eq
    (stage : concreteStageBase) :
    Iut.SourceModelFrobenioid.Carrier.effectiveRationalFunctionSubmonoid
        (Phi := concreteStageModelDivisorialMonoid)
        (data := concreteStageModelInput)
        (Iut.SourceModelFrobenioid.Carrier.zeroObject
          concreteStageModelDivisorialMonoid concreteStageModelInput stage) =
      Iut.SourceFinitePlaceReconstruction.stageEffectiveRationalFunctionSubmonoid
        concretePlace stage.unop := by
  exact Iut.SourceFinitePlaceReconstruction.stageModelEffectiveSubmonoid_eq
    concretePlace stage

theorem source_stage_effective_equiv_natural
    {source target : concreteStageBase} (arrow : source ⟶ target) :
    (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveRationalFunctionEquivIntegralMonoid
      concretePlace source).toMonoidHom.comp
        (Iut.SourceModelFrobenioid.Carrier.effectiveRationalFunctionPullback
          (Phi := concreteStageModelDivisorialMonoid)
          (data := concreteStageModelInput) arrow) =
      (Iut.SourceFinitePlaceReconstruction.stageIntegralTransition concretePlace
        arrow.unop.le).hom.comp
        (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveRationalFunctionEquivIntegralMonoid
          concretePlace target).toMonoidHom := by
  exact stageModelEffectiveRationalFunctionEquivIntegralMonoid_natural
    concretePlace arrow

theorem source_stage_effective_natIso_component
    (stage : (concreteStageBase)ᵒᵖ) :
    (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveToIntegralNatIso concretePlace).hom.app
        stage =
      MonCat.ofHom
        (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveRationalFunctionEquivIntegralMonoid
          concretePlace stage.unop).toMonoidHom := by
  rfl

theorem source_stage_effective_natIso_inv_component
    (stage : (concreteStageBase)ᵒᵖ) :
    (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveToIntegralNatIso concretePlace).inv.app
        stage =
      MonCat.ofHom
        (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveRationalFunctionEquivIntegralMonoid
          concretePlace stage.unop).symm.toMonoidHom := by
  rfl

theorem source_stage_zero_natIso_component
    (stage : (concreteStageBase)ᵒᵖ) :
    (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectToIntegralNatIso concretePlace).hom.app
        stage =
      (Iut.SourceModelFrobenioid.Carrier.zeroRationalFunctionNatIso
        (Phi := concreteStageModelDivisorialMonoid)
        (data := concreteStageModelInput)).hom.app stage ≫
        (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveToIntegralNatIso
          concretePlace).hom.app stage := by
  rfl

theorem source_stage_zero_natIso_inv_component
    (stage : (concreteStageBase)ᵒᵖ) :
    (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectToIntegralNatIso concretePlace).inv.app
        stage =
      (Iut.SourceFinitePlaceReconstruction.stageModelEffectiveToIntegralNatIso
        concretePlace).inv.app stage ≫
        (Iut.SourceModelFrobenioid.Carrier.zeroRationalFunctionNatIso
          (Phi := concreteStageModelDivisorialMonoid)
          (data := concreteStageModelInput)).inv.app stage := by
  rfl

theorem source_stage_integral_transition_apply
    {source target : concreteStageIndex} (map : source ≤ target)
    (value : Iut.SourceFinitePlaceReconstruction.StageIntegralMonoid concretePlace source) :
    (Iut.SourceFinitePlaceReconstruction.stageIntegralTransition concretePlace map value).1 =
      Iut.SourceFinitePlaceReconstruction.transitionContinuousLinearMap concretePlace map
        value.1 := by
  rfl

theorem source_stage_integral_transition_trans
    {first second third : concreteStageIndex}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    (Iut.SourceFinitePlaceReconstruction.stageIntegralTransition concretePlace firstSecond).comp
        (Iut.SourceFinitePlaceReconstruction.stageIntegralTransition concretePlace secondThird) =
      Iut.SourceFinitePlaceReconstruction.stageIntegralTransition concretePlace
        (firstSecond.trans secondThird) := by
  exact Iut.SourceFinitePlaceReconstruction.stageIntegralTransition_trans
    concretePlace firstSecond secondThird

theorem source_stage_integral_functor_obj
    (stage : (concreteStageBase)ᵒᵖ) :
    (concreteStageIntegralFunctor.obj stage).carrier =
      Iut.SourceFinitePlaceReconstruction.StageIntegralMonoid concretePlace stage.unop.unop := by
  rfl

theorem source_stage_integral_functor_map
    {source target : (concreteStageBase)ᵒᵖ} (arrow : source ⟶ target) :
    (concreteStageIntegralFunctor.map arrow).hom =
      (Iut.SourceFinitePlaceReconstruction.stageIntegralTransition concretePlace
        arrow.unop.unop.le).hom := by
  rfl

theorem source_stage_integral_cocone_component
    (stage : (concreteStageBase)ᵒᵖ) :
    (Iut.SourceFinitePlaceReconstruction.stageIntegralToIndCocone concretePlace).ι.app stage =
      MonCat.ofHom
        (Iut.SourceFinitePlaceReconstruction.stageIntegralToIndHom concretePlace
          stage.unop.unop) := by
  rfl

theorem source_stage_integral_colimit_to_ind_cocone
    (stage : (concreteStageBase)ᵒᵖ) :
    (MonCat.FilteredColimits.coconeMorphism concreteStageIntegralFunctor stage) ≫
        (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToInd concretePlace) =
      (Iut.SourceFinitePlaceReconstruction.stageIntegralToIndCocone concretePlace).ι.app stage := by
  exact Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToInd_cocone
    concretePlace stage

theorem source_stage_integral_colimit_to_ind_surjective :
    Function.Surjective
      (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToInd concretePlace) := by
  exact Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToInd_surjective
    concretePlace

theorem source_stage_integral_colimit_to_ind_injective :
    Function.Injective
      (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToInd concretePlace) := by
  exact Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToInd_injective
    concretePlace

theorem source_stage_integral_colimit_to_ind_bijective :
    Function.Bijective
      (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToInd concretePlace) := by
  exact ⟨source_stage_integral_colimit_to_ind_injective,
    source_stage_integral_colimit_to_ind_surjective⟩

theorem source_stage_integral_colimit_equiv_ind_apply
    (value : concreteStageIntegralColimit.carrier) :
    Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd concretePlace
        value =
      Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToInd
        concretePlace value := by
  rfl

theorem source_stage_integral_colimit_equiv_ind_injective :
    Function.Injective
      (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd concretePlace) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd
    concretePlace).injective

theorem source_stage_integral_colimit_equiv_ind_surjective :
    Function.Surjective
      (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd concretePlace) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd
    concretePlace).surjective

theorem source_stage_integral_colimit_equiv_ind_mul
    (first second : concreteStageIntegralColimit.carrier) :
    Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd concretePlace
        (first * second) =
      Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd
        concretePlace first *
        Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd
          concretePlace second := by
  exact
    (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd
      concretePlace).map_mul first second

theorem source_stage_integral_colimit_equiv_ind_one :
    Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd concretePlace
        (1 : concreteStageIntegralColimit.carrier) = 1 := by
  exact (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd
    concretePlace).map_one

theorem source_stage_zero_colimit_to_integral_cocone
    (stage : (concreteStageBase)ᵒᵖ) :
    (MonCat.FilteredColimits.coconeMorphism concreteStageZeroFunctor stage) ≫
        (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitToIntegral
          concretePlace) =
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectToIntegralNatIso
        concretePlace).hom.app stage ≫
        MonCat.FilteredColimits.coconeMorphism concreteStageIntegralFunctor stage := by
  exact Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitToIntegral_cocone
    concretePlace stage

theorem source_stage_integral_to_zero_colimit_cocone
    (stage : (concreteStageBase)ᵒᵖ) :
    (MonCat.FilteredColimits.coconeMorphism concreteStageIntegralFunctor stage) ≫
        (Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToModelZeroObject
          concretePlace) =
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectToIntegralNatIso
        concretePlace).inv.app stage ≫
        MonCat.FilteredColimits.coconeMorphism concreteStageZeroFunctor stage := by
  exact Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToModelZeroObject_cocone
    concretePlace stage

theorem source_stage_zero_colimit_iso_hom_apply
    (value : concreteStageZeroColimit.carrier) :
    (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitIsoIntegral
      concretePlace).hom value =
      Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitToIntegral
        concretePlace value := by
  rfl

theorem source_stage_zero_colimit_iso_inv_apply
    (value : concreteStageIntegralColimit.carrier) :
    (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitIsoIntegral
      concretePlace).inv value =
      Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitToModelZeroObject
        concretePlace value := by
  rfl

theorem source_stage_zero_colimit_equiv_ind_apply
    (value : concreteStageZeroColimit.carrier) :
    Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivInd
        concretePlace value =
      Iut.SourceFinitePlaceReconstruction.stageIntegralFilteredColimitEquivInd concretePlace
        ((Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitIsoIntegral
          concretePlace).hom value) := by
  rfl

theorem source_stage_zero_colimit_equiv_sourceMLF_apply
    (value : concreteStageZeroColimit.carrier) :
    Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace value =
      Iut.SourceFinitePlaceReconstruction.indIntegralMonoidEquivSourceMLF concretePlace
        (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivInd
          concretePlace value) := by
  rfl

theorem source_stage_zero_colimit_equiv_ind_injective :
    Function.Injective
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivInd
        concretePlace) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivInd
    concretePlace).injective

theorem source_stage_zero_colimit_equiv_ind_surjective :
    Function.Surjective
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivInd
        concretePlace) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivInd
    concretePlace).surjective

theorem source_stage_zero_colimit_equiv_sourceMLF_injective :
    Function.Injective
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
    concretePlace).injective

theorem source_stage_zero_colimit_equiv_sourceMLF_surjective :
    Function.Surjective
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
    concretePlace).surjective

theorem source_stage_model_frobenioid_preFrobenioid_presentation :
    concreteStageModel.toPreFrobenioidPresentation.preFrobenioid =
      concreteStageModel.preFrobenioid := by
  rfl

theorem source_stage_model_base_is_connected :
    CategoryTheory.IsConnected concreteStageBase := by
  exact concreteStageModel.baseConnected

theorem source_stage_model_base_arrow_epi
    {source target : concreteStageBase} (arrow : source ⟶ target) :
    Epi arrow := by
  exact concreteStageModel.baseTotallyEpimorphic arrow

theorem source_stage_model_zero_object_base
    (stage : concreteStageBase) :
    Iut.SourceModelFrobenioid.Object.base
      (Iut.SourceModelFrobenioid.Carrier.zeroObject
        concreteStageModelDivisorialMonoid concreteStageModelInput stage) = stage := by
  rfl

theorem source_stage_model_zero_object_divisor
    (stage : concreteStageBase) :
    Iut.SourceModelFrobenioid.Object.divisorClass
      (Iut.SourceModelFrobenioid.Carrier.zeroObject
        concreteStageModelDivisorialMonoid concreteStageModelInput stage) = 0 := by
  rfl

theorem source_stage_model_zero_object_rational_equiv_apply
    (stage : concreteStageBase)
    (value :
      (concreteStageModel.preFrobenioid.LinearBaseIdentityEndomorphism
        (Iut.SourceModelFrobenioid.Carrier.zeroObject
          concreteStageModelDivisorialMonoid concreteStageModelInput stage))) :
    Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
      concretePlace stage value =
      Iut.SourceFinitePlaceReconstruction.stageModelEffectiveRationalFunctionEquivIntegralMonoid
        concretePlace stage
        ((Iut.SourceModelFrobenioid.Carrier.zeroObjectRationalFunctionEquiv
          (Phi := concreteStageModelDivisorialMonoid)
          (data := concreteStageModelInput) stage) value) := by
  rfl

theorem source_stage_model_zero_object_rational_equiv_bijective
    (stage : concreteStageBase) :
    Function.Bijective
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
        concretePlace stage) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
    concretePlace stage).bijective

theorem source_stage_model_zero_object_rational_equiv_mul
    (stage : concreteStageBase)
    (first second :
      concreteStageModel.preFrobenioid.LinearBaseIdentityEndomorphism
        (Iut.SourceModelFrobenioid.Carrier.zeroObject
          concreteStageModelDivisorialMonoid concreteStageModelInput stage)) :
    Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
      concretePlace stage (first * second) =
      Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
        concretePlace stage first *
        Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
          concretePlace stage second := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
    concretePlace stage).map_mul first second

theorem source_stage_model_zero_object_rational_equiv_one
    (stage : concreteStageBase) :
    Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
      concretePlace stage 1 = 1 := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectRationalFunctionEquivIntegralMonoid
    concretePlace stage).map_one

theorem source_stage_model_zero_object_filtered_colimit_equiv_sourceMLF_mul
    (first second : concreteStageZeroColimit.carrier) :
    Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace (first * second) =
      Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace first *
        Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
          concretePlace second := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
    concretePlace).map_mul first second

theorem source_stage_model_zero_object_filtered_colimit_equiv_sourceMLF_one :
    Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace (1 : concreteStageZeroColimit.carrier) = 1 := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
    concretePlace).map_one

theorem source_stage_model_zero_object_filtered_colimit_equiv_sourceMLF_bijective :
    Function.Bijective
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace) := by
  exact (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
    concretePlace).bijective

theorem source_stage_model_zero_object_filtered_colimit_equiv_sourceMLF_injective :
    Function.Injective
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace) := by
  exact source_stage_model_zero_object_filtered_colimit_equiv_sourceMLF_bijective.1

theorem source_stage_model_zero_object_filtered_colimit_equiv_sourceMLF_surjective :
    Function.Surjective
      (Iut.SourceFinitePlaceReconstruction.stageModelZeroObjectFilteredColimitEquivSourceMLF
        concretePlace) := by
  exact source_stage_model_zero_object_filtered_colimit_equiv_sourceMLF_bijective.2

structure ConcreteSourceFrobenioidOutput (l : PrimeGeFive) where
  boundary : ConcreteSourceFrobenioidBoundary l
  stageModel : Iut.FrobenioidPresentation
  stageModel_eq : stageModel = concreteStageModel
  sourceMLF : Type
  sourceMLF_nonempty : Nonempty sourceMLF
  sourceMLF_eq : sourceMLF = concreteStageSourceMLF
  localFiniteKernel :
    boundary.cStage.localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ)

noncomputable def concreteSourceFrobenioidOutput (l : PrimeGeFive) :
    ConcreteSourceFrobenioidOutput l where
  boundary := concreteSourceFrobenioidBoundary l
  stageModel := concreteStageModel
  stageModel_eq := rfl
  sourceMLF := concreteStageSourceMLF
  sourceMLF_nonempty := ⟨1⟩
  sourceMLF_eq := rfl
  localFiniteKernel := concreteInitialThetaCStage_local_finite_kernel l

@[simp] theorem source_output_boundary (l : PrimeGeFive) :
    (concreteSourceFrobenioidOutput l).boundary =
      concreteSourceFrobenioidBoundary l :=
  rfl

@[simp] theorem source_output_stageModel (l : PrimeGeFive) :
    (concreteSourceFrobenioidOutput l).stageModel = concreteStageModel :=
  (concreteSourceFrobenioidOutput l).stageModel_eq

@[simp] theorem source_output_sourceMLF (l : PrimeGeFive) :
    (concreteSourceFrobenioidOutput l).sourceMLF = concreteStageSourceMLF :=
  (concreteSourceFrobenioidOutput l).sourceMLF_eq

theorem source_output_kernel (l : PrimeGeFive) :
    (concreteSourceFrobenioidOutput l).boundary.cStage.localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) :=
  (concreteSourceFrobenioidOutput l).localFiniteKernel

end ConcreteSourceFrobenioidBridge

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSourceFrobenioidBridge : Obligation :=
  { id := "IUT-I-II.concrete-source-frobenioid-bridge"
    source := "IUT I-II, Frobenioids I Definition 5.2 and IUT II Definition 4.9"
    status := VerificationStatus.testCarrier
    note :=
      "The source finite-place reconstruction and its model Frobenioid " ++
        "presentation are instantiated at the actual Q(i) place above 5. " ++
        "Normalized divisor transitions, effective rational functions, the " ++
        "finite-stage integral functor, filtered-colimit equivalences, the " ++
        "zero-object rational monoid, and the source MLF integral monoid are " ++
        "exposed through a concrete bridge to the C-stage finite kernel. " ++
        "This proves a source model presentation and its arithmetic evaluation; " ++
        "it does not assert etale recognition, Tate point uniformization, or a " ++
        "source theta-link."
    dependsOn :=
      [ "IUT-I-II.concrete-initial-theta-c-stage",
        "IUT-I-II.source-finite-stage-model-frobenioid",
        "IUT-I-II.source-finite-stage-model-evaluation",
        "IUT-II.MLF-integral-monoid-comparison" ] }

end LeanFormal.IUT.Audit
