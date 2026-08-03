/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteLocalMLFComparison

/-!
# Finite-place reconstruction for IUT I, Definition 5.2(v)

This file constructs the ind-topology on the algebraic closure of an actual
number-field completion from its finite Galois local subfields. It then
restricts the colimit to the nonzero integral elements and identifies the
resulting monoid with `O_(Kbar)^triangle`.
-/

open CategoryTheory
namespace Iut

universe u

set_option synthInstance.maxHeartbeats 200000 in
-- The iterated scalar actions `Q_p -> K_v -> E` require deeper typeclass search.
section

namespace SourceFinitePlaceReconstruction

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

abbrev Base (place : NumberField.FinitePlace K) :=
  ThetaFinitePlace.Completion place

abbrev RationalBase (place : NumberField.FinitePlace K) :=
  ThetaFinitePlace.Completion (ThetaFinitePlace.comap (k := ℚ) place)

abbrev Closure (place : NumberField.FinitePlace K) :=
  AlgebraicClosure (Base place)

noncomputable instance closureNormedField
    (place : NumberField.FinitePlace K) : NormedField (Closure place) :=
  spectralNorm.normedField (Base place) (Closure place)

noncomputable instance closureNormedAlgebra
    (place : NumberField.FinitePlace K) :
    NormedAlgebra (Base place) (Closure place) :=
  spectralNorm.normedAlgebra (Base place) (Closure place)

abbrev StageIndex (place : NumberField.FinitePlace K) :=
  FiniteGaloisIntermediateField (Base place) (Closure place)

noncomputable instance stageFiniteDimensionalRational
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    FiniteDimensional (RationalBase place) stage := by
  letI : FiniteDimensional (RationalBase place) (Base place) :=
    ThetaFinitePlace.finiteDimensional place
  letI : FiniteDimensional (Base place) stage := inferInstance
  exact FiniteDimensional.trans (RationalBase place) (Base place) stage

noncomputable instance stageContinuousSMulRational
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    ContinuousSMul (RationalBase place) stage := by
  apply continuousSMul_of_algebraMap
  convert
    (continuous_algebraMap (Base place) stage).comp
      (ThetaFinitePlace.continuous_completionRingHom place) using 1

noncomputable instance stageCompleteSpace
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    CompleteSpace stage :=
  FiniteDimensional.complete (Base place) stage

noncomputable instance stageLocallyCompactSpace
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    LocallyCompactSpace stage :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (RationalBase place) stage

noncomputable instance stageSecondCountableTopology
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    SecondCountableTopology stage := by
  let dimension := Module.finrank (RationalBase place) stage
  let equivalence :
      stage ≃L[RationalBase place] Fin dimension → RationalBase place :=
    ContinuousLinearEquiv.ofFinrankEq
      (Module.finrank_fin_fun (RationalBase place)).symm
  exact equivalence.toHomeomorph.secondCountableTopology

noncomputable def transitionLinearMap
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    source →ₗ[RationalBase place] target :=
  (IntermediateField.inclusion map).toLinearMap.restrictScalars
    (RationalBase place)

noncomputable def transitionContinuousLinearMap
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    source →L[RationalBase place] target :=
  (transitionLinearMap place map).mkContinuous 1 (fun value => by
    simp [transitionLinearMap])

noncomputable instance stageDecidableEq
    (place : NumberField.FinitePlace K) :
    DecidableEq (StageIndex place) := Classical.decEq _

noncomputable instance transitionDirectedSystem
    (place : NumberField.FinitePlace K) :
    DirectedSystem (fun stage : StageIndex place => stage)
      (fun _source _target map => transitionLinearMap place map) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

noncomputable abbrev stageDiagram
    (place : NumberField.FinitePlace K) :
    StageIndex place ⥤ TopModuleCat (RationalBase place) where
  obj stage := TopModuleCat.of (RationalBase place) stage
  map map := TopModuleCat.ofHom (transitionContinuousLinearMap place map.le)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

noncomputable def moduleCocone
    (place : NumberField.FinitePlace K) :
    Limits.Cocone
      (stageDiagram place ⋙
        forget₂ (TopModuleCat (RationalBase place))
          (ModuleCat (RationalBase place))) :=
  ModuleCat.directLimitCocone
    (fun stage : StageIndex place => stage)
    (fun _source _target map => transitionLinearMap place map)

noncomputable def moduleIsColimit
    (place : NumberField.FinitePlace K) :
    Limits.IsColimit (moduleCocone place) :=
  ModuleCat.directLimitIsColimit
    (fun stage : StageIndex place => stage)
    (fun _source _target map => transitionLinearMap place map)

noncomputable abbrev module
    (place : NumberField.FinitePlace K) :
    SourceIndTopologicalLocalModule
      (.finite (ThetaFinitePlace.comap (k := ℚ) place)) where
  stageIndex := StageIndex place
  stageDiagram := stageDiagram place
  stage_finiteDimensional := fun stage => by infer_instance
  colimitCocone := TopModuleCat.ofCocone (moduleCocone place)
  colimitIsColimit := TopModuleCat.isColimit (moduleIsColimit place)

noncomputable def toAlgebraicClosureLinearMap
    (place : NumberField.FinitePlace K) :
    (module place).carrier →ₗ[RationalBase place] Closure place :=
  Module.DirectLimit.lift
    (RationalBase place) (StageIndex place)
    (fun stage : StageIndex place => stage)
    (fun _source _target map => transitionLinearMap place map)
    (fun stage =>
      stage.toIntermediateField.val.toLinearMap.restrictScalars
        (RationalBase place))
    (fun _ _ _ _ => rfl)

theorem toAlgebraicClosureLinearMap_injective
    (place : NumberField.FinitePlace K) :
    Function.Injective (toAlgebraicClosureLinearMap place) := by
  apply Module.DirectLimit.lift_injective
  intro stage
  exact stage.toIntermediateField.val.injective

theorem toAlgebraicClosureLinearMap_surjective
    (place : NumberField.FinitePlace K) :
    Function.Surjective (toAlgebraicClosureLinearMap place) := by
  intro value
  let stage : StageIndex place :=
    FiniteGaloisIntermediateField.adjoin
      (Base place) ({value} : Set (Closure place))
  have hvalue : value ∈ stage.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin
      (Base place) ({value} : Set (Closure place)) (Set.mem_singleton value)
  let stageValue : stage := ⟨value, hvalue⟩
  refine ⟨Module.DirectLimit.of
    (RationalBase place) (StageIndex place)
    (fun stage : StageIndex place => stage)
    (fun _source _target map => transitionLinearMap place map)
    stage stageValue, ?_⟩
  dsimp only [toAlgebraicClosureLinearMap]
  calc
    _ = stage.toIntermediateField.val.toLinearMap.restrictScalars
          (RationalBase place) stageValue :=
      Module.DirectLimit.lift_of
        (fun stage : StageIndex place =>
          stage.toIntermediateField.val.toLinearMap.restrictScalars
            (RationalBase place))
        (fun (_source _target : StageIndex place)
          (_map : _source ≤ _target) (_value : _source) => rfl)
        stageValue
    _ = value := rfl

noncomputable def carrierEquivAlgebraicClosure
    (place : NumberField.FinitePlace K) :
    (module place).carrier ≃ₗ[RationalBase place] Closure place :=
  LinearEquiv.ofBijective (toAlgebraicClosureLinearMap place)
    ⟨toAlgebraicClosureLinearMap_injective place,
      toAlgebraicClosureLinearMap_surjective place⟩

noncomputable instance carrierCommMonoid
    (place : NumberField.FinitePlace K) :
    CommMonoid (module place).carrier :=
  (carrierEquivAlgebraicClosure place).toEquiv.commMonoid

noncomputable def carrierMulEquivAlgebraicClosure
    (place : NumberField.FinitePlace K) :
    (module place).carrier ≃* Closure place :=
  Equiv.mulEquiv (carrierEquivAlgebraicClosure place).toEquiv

noncomputable def integralMonoidSubmonoid
    (place : NumberField.FinitePlace K) :
    Submonoid (module place).carrier where
  carrier value :=
    IsIntegral
        (Valuation.integer (ValuativeRel.valuation (Base place)))
        (carrierMulEquivAlgebraicClosure place value) ∧
      carrierMulEquivAlgebraicClosure place value ≠ 0
  one_mem' := by
    constructor
    · simpa using isIntegral_one
    · simp
  mul_mem' := by
    intro first second hfirst hsecond
    constructor
    · rw [map_mul]
      exact hfirst.1.mul hsecond.1
    · rw [map_mul]
      exact mul_ne_zero hfirst.2 hsecond.2

noncomputable abbrev IndIntegralMonoid
    (place : NumberField.FinitePlace K) :=
  integralMonoidSubmonoid place

noncomputable def stageIntegralMonoidSubmonoid
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Submonoid stage where
  carrier value :=
    IsIntegral
        (Valuation.integer (ValuativeRel.valuation (Base place)))
        (value : Closure place) ∧
      (value : Closure place) ≠ 0
  one_mem' := by
    constructor
    · simpa using isIntegral_one
    · simp
  mul_mem' := by
    intro first second hfirst hsecond
    constructor
    · exact hfirst.1.mul hsecond.1
    · exact mul_ne_zero hfirst.2 hsecond.2

noncomputable abbrev StageIntegralMonoid
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :=
  stageIntegralMonoidSubmonoid place stage

noncomputable def stageToCarrier
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    stage →* (module place).carrier where
  toFun value :=
    (carrierMulEquivAlgebraicClosure place).symm (value : Closure place)
  map_one' := by simp
  map_mul' _ _ := by simp

theorem carrierMulEquiv_stageToCarrier
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (value : stage) :
    carrierMulEquivAlgebraicClosure place (stageToCarrier place stage value) =
      (value : Closure place) := by
  simp [stageToCarrier]

theorem stageToCarrier_eq_colimit_ι
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (value : stage) :
    stageToCarrier place stage value =
      (module place).colimitCocone.ι.app stage value := by
  apply (carrierMulEquivAlgebraicClosure place).injective
  rw [carrierMulEquiv_stageToCarrier]
  change
    (value : Closure place) =
      toAlgebraicClosureLinearMap place
        ((module place).colimitCocone.ι.app stage value)
  symm
  exact Module.DirectLimit.lift_of
    (fun stage : StageIndex place =>
      stage.toIntermediateField.val.toLinearMap.restrictScalars
        (RationalBase place))
    (fun (_source _target : StageIndex place)
      (_map : _source ≤ _target) (_value : _source) => rfl)
    value

theorem continuous_stageToCarrier
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Continuous (stageToCarrier place stage) := by
  have hcontinuous :
      Continuous fun value : stage =>
        (module place).colimitCocone.ι.app stage value :=
    (module place).colimitCocone.ι.app stage |>.hom.continuous
  convert hcontinuous using 1
  ext value
  exact stageToCarrier_eq_colimit_ι place stage value

noncomputable def stageIntegralToInd
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    StageIntegralMonoid place stage →* IndIntegralMonoid place where
  toFun value :=
    ⟨stageToCarrier place stage value.1, by
      constructor
      · simpa only [carrierMulEquiv_stageToCarrier] using value.2.1
      · simpa only [carrierMulEquiv_stageToCarrier] using value.2.2⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

theorem continuous_stageIntegralToInd
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Continuous (stageIntegralToInd place stage) := by
  apply Continuous.subtype_mk
  exact (continuous_stageToCarrier place stage).comp continuous_subtype_val

theorem exists_stage_representation
    (place : NumberField.FinitePlace K) (value : IndIntegralMonoid place) :
    ∃ (stage : StageIndex place) (stageValue : StageIntegralMonoid place stage),
      stageIntegralToInd place stage stageValue = value := by
  let algebraicValue : Closure place :=
    carrierMulEquivAlgebraicClosure place value.1
  let stage : StageIndex place :=
    FiniteGaloisIntermediateField.adjoin
      (Base place) ({algebraicValue} : Set (Closure place))
  have hvalue : algebraicValue ∈ stage.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin
      (Base place) ({algebraicValue} : Set (Closure place))
      (Set.mem_singleton algebraicValue)
  let stageValue : stage := ⟨algebraicValue, hvalue⟩
  have hstageValue :
      stageValue ∈ stageIntegralMonoidSubmonoid place stage := by
    constructor
    · exact value.2.1
    · exact value.2.2
  refine ⟨stage, ⟨stageValue, hstageValue⟩, ?_⟩
  apply Subtype.ext
  apply (carrierMulEquivAlgebraicClosure place).injective
  change
    carrierMulEquivAlgebraicClosure place
        (stageToCarrier place stage stageValue) =
      carrierMulEquivAlgebraicClosure place value.1
  rw [carrierMulEquiv_stageToCarrier]

noncomputable def indIntegralMonoidEquivSourceMLF
    (place : NumberField.FinitePlace K) :
    IndIntegralMonoid place ≃* SourceMLFIntegralMonoid (Base place) where
  toFun value :=
    ⟨⟨carrierMulEquivAlgebraicClosure place value.1, value.2.1⟩,
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro equality
        exact value.2.2 (congrArg Subtype.val equality))⟩
  invFun value :=
    ⟨(carrierMulEquivAlgebraicClosure place).symm value.1.1,
      by
        constructor
        · simpa only [MulEquiv.apply_symm_apply] using value.1.2
        · have hvalue : value.1.1 ≠ 0 := by
            intro equality
            exact nonZeroDivisors.coe_ne_zero value (Subtype.ext equality)
          simpa only [MulEquiv.apply_symm_apply] using hvalue⟩
  left_inv value := by
    apply Subtype.ext
    exact (carrierMulEquivAlgebraicClosure place).symm_apply_apply value.1
  right_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    exact (carrierMulEquivAlgebraicClosure place).apply_symm_apply value.1.1
  map_mul' first second := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- The absolute Galois automorphism transported to the ind-topological carrier. -/
noncomputable def indGaloisMulAut
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    MulAut (IndIntegralMonoid place) :=
  (indIntegralMonoidEquivSourceMLF place).trans
    ((SourceMLFIntegralMonoid.galoisMulAut (Base place) sigma).trans
      (indIntegralMonoidEquivSourceMLF place).symm)

/-- Conjugation through the multiplicative identification intertwines the two actions. -/
theorem indIntegralMonoidEquivSourceMLF_indGaloisMulAut
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : IndIntegralMonoid place) :
    indIntegralMonoidEquivSourceMLF place (indGaloisMulAut place sigma value) =
      SourceMLFIntegralMonoid.galoisMulAut (Base place) sigma
        (indIntegralMonoidEquivSourceMLF place value) := by
  simp only [indGaloisMulAut, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- The literal Krull Galois action on the ind-topological integral monoid. -/
noncomputable def indGaloisAction
    (place : NumberField.FinitePlace K) :
    (Closure place ≃ₐ[Base place] Closure place) →*
      MulAut (IndIntegralMonoid place) where
  toFun sigma := indGaloisMulAut place sigma
  map_one' := by
    apply MulEquiv.ext
    intro value
    apply (indIntegralMonoidEquivSourceMLF place).injective
    rw [indIntegralMonoidEquivSourceMLF_indGaloisMulAut]
    change SourceMLFIntegralMonoid.galoisAction (Base place) 1
        (indIntegralMonoidEquivSourceMLF place value) = _
    rw [map_one]
    rfl
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    apply (indIntegralMonoidEquivSourceMLF place).injective
    rw [indIntegralMonoidEquivSourceMLF_indGaloisMulAut]
    change SourceMLFIntegralMonoid.galoisAction (Base place) (first * second)
        (indIntegralMonoidEquivSourceMLF place value) = _
    change
      SourceMLFIntegralMonoid.galoisAction (Base place) (first * second)
          (indIntegralMonoidEquivSourceMLF place value) =
        indIntegralMonoidEquivSourceMLF place
          ((indGaloisMulAut place first) ((indGaloisMulAut place second) value))
    rw [indIntegralMonoidEquivSourceMLF_indGaloisMulAut]
    rw [indIntegralMonoidEquivSourceMLF_indGaloisMulAut]
    exact congrArg
      (fun automorphism : MulAut (SourceMLFIntegralMonoid (Base place)) =>
        automorphism (indIntegralMonoidEquivSourceMLF place value))
      (map_mul (SourceMLFIntegralMonoid.galoisAction (Base place)) first second)

/-- The monoid identification intertwines the transported and literal Galois actions. -/
theorem indIntegralMonoidEquivSourceMLF_galois
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : IndIntegralMonoid place) :
    indIntegralMonoidEquivSourceMLF place
        (indGaloisAction place sigma value) =
      SourceMLFIntegralMonoid.galoisMulAut (Base place) sigma
        (indIntegralMonoidEquivSourceMLF place value) := by
  exact indIntegralMonoidEquivSourceMLF_indGaloisMulAut place sigma value

end

end SourceFinitePlaceReconstruction

end

end Iut
