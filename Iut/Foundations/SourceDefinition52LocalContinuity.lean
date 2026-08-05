/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceDefinition52LocalReconstruction

/-!
# Continuous finite-place Galois action for IUT I, Definition 5.2(v)-(vi)

Every finite Galois intermediate field is stable under the absolute Galois
group. Restriction therefore acts continuously at every finite-dimensional
stage, and the final topology on the filtered colimit makes every induced
automorphism continuous on the ind-topological integral monoid.  Joint
continuity in the group and monoid variables is treated separately.
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

/-- Restriction of an absolute Galois automorphism to a finite Galois stage. -/
noncomputable def stageGaloisContinuousLinearEquiv
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    stage ≃L[RationalBase place] stage :=
  ((sigma.restrictNormal stage.toIntermediateField).toLinearEquiv.restrictScalars
    (RationalBase place)).toContinuousLinearEquiv

theorem stageGaloisContinuousLinearEquiv_coe
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (sigma : Closure place ≃ₐ[Base place] Closure place) (value : stage) :
    ((stageGaloisContinuousLinearEquiv place stage sigma value : stage) :
        Closure place) = sigma value := by
  exact AlgEquiv.restrictNormal_apply stage.toIntermediateField sigma value

theorem transition_galois_commutes
    (place : NumberField.FinitePlace K) {source target : StageIndex place}
    (map : source ⟶ target)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    (stageDiagram place).map map ≫
        TopModuleCat.ofHom
          (stageGaloisContinuousLinearEquiv place target sigma).toContinuousLinearMap =
      TopModuleCat.ofHom
          (stageGaloisContinuousLinearEquiv place source sigma).toContinuousLinearMap ≫
        (stageDiagram place).map map := by
  ext value
  change
    (((stageGaloisContinuousLinearEquiv place target sigma
        (transitionContinuousLinearMap place map.le value) : target) :
          Closure place)) =
      (((transitionContinuousLinearMap place map.le
        (stageGaloisContinuousLinearEquiv place source sigma value) : target) :
          Closure place))
  rw [stageGaloisContinuousLinearEquiv_coe]
  dsimp only [transitionContinuousLinearMap, transitionLinearMap]
  simp only [LinearMap.mkContinuous_apply, LinearMap.coe_restrictScalars]
  change sigma (value : Closure place) =
    ((stageGaloisContinuousLinearEquiv place source sigma value : source) :
      Closure place)
  exact (stageGaloisContinuousLinearEquiv_coe place source sigma value).symm

/-- The stagewise Galois maps, followed by the colimit inclusions, form a cocone. -/
noncomputable def galoisCocone
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    Limits.Cocone (stageDiagram place) where
  pt := (module place).colimitCocone.pt
  ι := {
    app := fun stage =>
      TopModuleCat.ofHom
          (stageGaloisContinuousLinearEquiv place stage sigma).toContinuousLinearMap ≫
        (module place).colimitCocone.ι.app stage
    naturality := by
      intro source target map
      simp only [Functor.const_obj_map]
      rw [← Category.assoc, transition_galois_commutes place map sigma]
      rw [Category.assoc]
      exact congrArg
        (fun arrow =>
          TopModuleCat.ofHom
              (stageGaloisContinuousLinearEquiv place source sigma).toContinuousLinearMap ≫
            arrow)
        ((module place).colimitCocone.w map) }

/-- The absolute Galois automorphism induced on the topological colimit. -/
noncomputable def galoisContinuousLinearMap
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    (module place).carrier →L[RationalBase place] (module place).carrier :=
  ((module place).colimitIsColimit.desc (galoisCocone place sigma)).hom

theorem galoisContinuousLinearMap_stage
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (sigma : Closure place ≃ₐ[Base place] Closure place) (value : stage) :
    galoisContinuousLinearMap place sigma
        ((module place).colimitCocone.ι.app stage value) =
      (module place).colimitCocone.ι.app stage
        (stageGaloisContinuousLinearEquiv place stage sigma value) := by
  have hfac := (module place).colimitIsColimit.fac (galoisCocone place sigma) stage
  exact congrArg (fun map => map value) hfac

/-- The continuous colimit action is the literal action on the algebraic closure. -/
theorem carrierMulEquiv_galoisContinuousLinearMap
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : (module place).carrier) :
    carrierMulEquivAlgebraicClosure place
        (galoisContinuousLinearMap place sigma value) =
      sigma (carrierMulEquivAlgebraicClosure place value) := by
  rcases Module.DirectLimit.exists_of
      (R := RationalBase place) (ι := StageIndex place)
      (G := fun stage : StageIndex place => stage)
      (f := fun _source _target map => transitionLinearMap place map)
      value with ⟨stage, stageValue, hvalue⟩
  rw [← hvalue]
  have hof :
      Module.DirectLimit.of
          (RationalBase place) (StageIndex place)
          (fun stage : StageIndex place => stage)
          (fun _source _target map => transitionLinearMap place map)
          stage stageValue =
        (module place).colimitCocone.ι.app stage stageValue := rfl
  rw [hof]
  rw [galoisContinuousLinearMap_stage]
  rw [← stageToCarrier_eq_colimit_ι]
  rw [← stageToCarrier_eq_colimit_ι]
  rw [carrierMulEquiv_stageToCarrier]
  rw [carrierMulEquiv_stageToCarrier]
  exact stageGaloisContinuousLinearEquiv_coe place stage sigma stageValue

theorem galoisContinuousLinearMap_one
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    galoisContinuousLinearMap place sigma 1 = 1 := by
  apply (carrierMulEquivAlgebraicClosure place).injective
  rw [carrierMulEquiv_galoisContinuousLinearMap]
  simp only [map_one]

theorem galoisContinuousLinearMap_mul
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (first second : (module place).carrier) :
    galoisContinuousLinearMap place sigma (first * second) =
      galoisContinuousLinearMap place sigma first *
        galoisContinuousLinearMap place sigma second := by
  apply (carrierMulEquivAlgebraicClosure place).injective
  rw [carrierMulEquiv_galoisContinuousLinearMap]
  rw [map_mul]
  rw [map_mul (carrierMulEquivAlgebraicClosure place)]
  rw [carrierMulEquiv_galoisContinuousLinearMap]
  rw [carrierMulEquiv_galoisContinuousLinearMap]
  exact map_mul sigma _ _

/-- The transported integral action is the restriction of the continuous colimit map. -/
theorem indGaloisMulAut_val_eq_galoisContinuousLinearMap
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : IndIntegralMonoid place) :
    (indGaloisMulAut place sigma value).1 =
      galoisContinuousLinearMap place sigma value.1 := by
  apply (carrierMulEquivAlgebraicClosure place).injective
  rw [carrierMulEquiv_galoisContinuousLinearMap]
  have hintertwining :=
    indIntegralMonoidEquivSourceMLF_indGaloisMulAut place sigma value
  exact congrArg
    (fun integralValue : SourceMLFIntegralMonoid (Base place) =>
      integralValue.1.1)
    hintertwining

/-- Every absolute Galois automorphism acts continuously on the ind-integral monoid. -/
theorem continuous_indGaloisMulAut
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    Continuous (indGaloisMulAut place sigma) := by
  apply Continuous.subtype_mk
  convert
    (galoisContinuousLinearMap place sigma).continuous.comp continuous_subtype_val using 1
  ext value
  exact indGaloisMulAut_val_eq_galoisContinuousLinearMap place sigma value

/-- The absolute Galois automorphism as a homeomorphic multiplicative equivalence. -/
noncomputable def indGaloisContinuousMulEquiv
    (place : NumberField.FinitePlace K)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    IndIntegralMonoid place ≃ₜ* IndIntegralMonoid place where
  __ := indGaloisMulAut place sigma
  continuous_toFun := continuous_indGaloisMulAut place sigma
  continuous_invFun := by
    change Continuous (indGaloisMulAut place sigma.symm)
    exact continuous_indGaloisMulAut place sigma.symm

theorem indGaloisContinuousMulEquiv_one
    (place : NumberField.FinitePlace K) :
    indGaloisContinuousMulEquiv place 1 =
      ContinuousMulEquiv.refl (IndIntegralMonoid place) := by
  apply ContinuousMulEquiv.ext
  intro value
  change indGaloisMulAut place 1 value = value
  exact congrArg
    (fun automorphism : MulAut (IndIntegralMonoid place) => automorphism value)
    (map_one (indGaloisAction place))

theorem indGaloisContinuousMulEquiv_mul
    (place : NumberField.FinitePlace K)
    (first second : Closure place ≃ₐ[Base place] Closure place) :
    indGaloisContinuousMulEquiv place (first * second) =
      (indGaloisContinuousMulEquiv place second).trans
        (indGaloisContinuousMulEquiv place first) := by
  apply ContinuousMulEquiv.ext
  intro value
  change indGaloisMulAut place (first * second) value =
    indGaloisMulAut place first (indGaloisMulAut place second value)
  exact congrArg
    (fun automorphism : MulAut (IndIntegralMonoid place) => automorphism value)
    (map_mul (indGaloisAction place) first second)

end

end SourceFinitePlaceReconstruction

end


end Iut
