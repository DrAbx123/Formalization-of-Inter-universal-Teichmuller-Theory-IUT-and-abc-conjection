/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceDefinition52LocalContinuity

/-!
# Joint finite-stage Galois continuity for IUT I, Definition 5.2(v)-(vi)

The Krull topology makes restriction from the absolute Galois group to every
finite Galois stage continuous.  Since the finite-stage Galois group is
discrete and acts by continuous linear equivalences, the resulting action on
each finite stage is jointly continuous.

This is the continuity statement needed at each level of the source
ind-system.  Joint continuity on the single `TopModuleCat` limit carrier would
require a separate continuity-with-parameters theorem and is not an automatic
consequence of its colimit universal property, which only controls linear maps
out of the colimit.
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

/-- Evaluation of finite-stage Galois automorphisms is jointly continuous. -/
theorem continuous_finiteStageGaloisEvaluation
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Continuous fun input :
        (stage ≃ₐ[Base place] stage) × stage =>
      input.1 input.2 := by
  rw [continuous_prod_of_discrete_left]
  intro sigma
  exact
    (LinearEquiv.toContinuousLinearEquiv
      (sigma.toLinearEquiv.restrictScalars (RationalBase place))).continuous

/-- The absolute Galois action on every finite normal stage is jointly continuous. -/
theorem continuous_stageGaloisAction
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Continuous fun input :
        (Closure place ≃ₐ[Base place] Closure place) × stage =>
      stageGaloisContinuousLinearEquiv place stage input.1 input.2 := by
  let restriction :
      (Closure place ≃ₐ[Base place] Closure place) →
        (stage ≃ₐ[Base place] stage) :=
    AlgEquiv.restrictNormalHom stage.toIntermediateField
  have hrestriction : Continuous restriction :=
    InfiniteGalois.restrictNormalHom_continuous stage.toIntermediateField
  have hpair : Continuous fun input :
      (Closure place ≃ₐ[Base place] Closure place) × stage =>
        (restriction input.1, input.2) :=
    (hrestriction.comp continuous_fst).prodMk continuous_snd
  convert
    (continuous_finiteStageGaloisEvaluation place stage).comp hpair using 1

/-- The ind-action on a value represented in a stage is the stage action followed by inclusion. -/
theorem indGaloisMulAut_stageIntegralToInd_val
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : StageIntegralMonoid place stage) :
    (indGaloisMulAut place sigma
        (stageIntegralToInd place stage value)).1 =
      stageToCarrier place stage
        (stageGaloisContinuousLinearEquiv place stage sigma value.1) := by
  rw [indGaloisMulAut_val_eq_galoisContinuousLinearMap]
  change
    galoisContinuousLinearMap place sigma
        (stageToCarrier place stage value.1) = _
  rw [stageToCarrier_eq_colimit_ι]
  rw [galoisContinuousLinearMap_stage]
  exact (stageToCarrier_eq_colimit_ι place stage _).symm

/-- Joint continuity of the colimit action after precomposition with one stage. -/
theorem continuous_galoisLinearMap_comp_stageToCarrier
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Continuous fun input :
        (Closure place ≃ₐ[Base place] Closure place) × stage =>
      galoisContinuousLinearMap place input.1
        (stageToCarrier place stage input.2) := by
  have hcarrier : Continuous fun input :
      (Closure place ≃ₐ[Base place] Closure place) × stage =>
        stageToCarrier place stage
          (stageGaloisContinuousLinearEquiv place stage input.1 input.2) :=
    (continuous_stageToCarrier place stage).comp
      (continuous_stageGaloisAction place stage)
  convert hcarrier using 1
  ext input
  rw [stageToCarrier_eq_colimit_ι]
  rw [galoisContinuousLinearMap_stage]
  exact (stageToCarrier_eq_colimit_ι place stage _).symm

/-- Joint continuity remains true after restricting a stage to its integral monoid
and including the result into the ind-integral monoid. -/
theorem continuous_indGaloisAction_comp_stageIntegralToInd
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Continuous fun input :
        (Closure place ≃ₐ[Base place] Closure place) ×
          StageIntegralMonoid place stage =>
      indGaloisMulAut place input.1
        (stageIntegralToInd place stage input.2) := by
  apply Continuous.subtype_mk
  let projection :
      (Closure place ≃ₐ[Base place] Closure place) ×
          StageIntegralMonoid place stage →
        (Closure place ≃ₐ[Base place] Closure place) × stage :=
    fun input => (input.1, input.2.1)
  have hprojection : Continuous projection :=
    continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hrestricted :=
    (continuous_galoisLinearMap_comp_stageToCarrier place stage).comp
      hprojection
  refine hrestricted.congr ?_
  intro input
  change
    galoisContinuousLinearMap place input.1
        (stageToCarrier place stage input.2.1) =
      (indGaloisMulAut place input.1
        (stageIntegralToInd place stage input.2)).1
  exact (indGaloisMulAut_val_eq_galoisContinuousLinearMap
    place input.1 (stageIntegralToInd place stage input.2)).symm

end

end SourceFinitePlaceReconstruction

end


end Iut
