/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceDefinition52LocalJointContinuity
import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# The finite-place ind-topological monoid of IUT I, Definition 5.2(v)

Absolute Anabelian Topics III, Section 0 uses `ind-` for an inductive system,
not merely for a topology on its limit carrier.  This file packages the
nonzero integral monoids in the finite Galois subfields of the algebraic
closure as a filtered system.  Every transition is a continuous monoid
homomorphism, the Krull group acts jointly continuously on every stage, and
all transitions are equivariant.

The source convention asks, strictly speaking, for a cofinal subsystem whose
ordered index is isomorphic to the positive integers.  The filtered system
constructed here is the canonical presentation by all finite Galois stages;
the arithmetic proof that it admits the required sequential cofinal subsystem
is kept in `SourceDefinition52Sequential`.
-/

open CategoryTheory
namespace Iut

universe u

/-- A filtered ind-system of topological monoids with a compatible continuous
action of one topological group at every stage. -/
structure SourceFilteredIndTopologicalMonoidAction
    (group : Type u) [Group group] [TopologicalSpace group] where
  Index : Type u
  [indexPreorder : Preorder Index]
  indexDirected :
    ∀ first second : Index,
      ∃ upper, first ≤ upper ∧ second ≤ upper
  stage : Index → TopologicalMonoidPresentation.{u}
  transition :
    ∀ {source target : Index}, source ≤ target →
      ContinuousMonoidHom (stage source) (stage target)
  transition_refl :
    ∀ index,
      transition (show index ≤ index from le_rfl) =
        ContinuousMonoidHom.id (stage index)
  transition_trans :
    ∀ {first second third : Index}
      (firstSecond : first ≤ second) (secondThird : second ≤ third),
      (transition firstSecond).comp (transition secondThird) =
        transition (firstSecond.trans secondThird)
  action : ∀ index, group →* MulAut (stage index).carrier
  continuous_action :
    ∀ index,
      Continuous fun input : group × (stage index).carrier =>
        action index input.1 input.2
  transition_equivariant :
    ∀ {source target : Index} (map : source ≤ target)
      (sigma : group) (value : (stage source).carrier),
      transition map (action source sigma value) =
        action target sigma (transition map value)

namespace SourceFilteredIndTopologicalMonoidAction

attribute [instance] indexPreorder

/-- The paper's strict sequential convention, stated as a cofinal monotone
choice of stages indexed by the natural numbers. -/
structure SequentialCofinalPresentation
    {group : Type u} [Group group] [TopologicalSpace group]
    (system : SourceFilteredIndTopologicalMonoidAction group) where
  stageIndex : ℕ → system.Index
  monotone_stageIndex : Monotone stageIndex
  cofinal_stageIndex : ∀ index, ∃ n, index ≤ stageIndex n

/-- An exhaustive algebraic limit of an ind-system.  The action on the limit
is algebraic; continuity belongs to the levelwise ind-presentation above. -/
structure ExhaustiveAlgebraicLimit
    {group : Type u} [Group group] [TopologicalSpace group]
    (system : SourceFilteredIndTopologicalMonoidAction group) where
  limit : Type u
  [limitMonoid : Monoid limit]
  inclusion :
    ∀ index, (system.stage index).carrier →* limit
  inclusion_injective :
    ∀ index, Function.Injective (inclusion index)
  inclusion_transition :
    ∀ {source target} (map : source ≤ target),
      (inclusion target).comp (system.transition map).hom =
        inclusion source
  exhausted :
    ∀ value : limit,
      ∃ (index : system.Index) (stageValue : (system.stage index).carrier),
        inclusion index stageValue = value
  limitAction : group →* MulAut limit
  inclusion_equivariant :
    ∀ index (sigma : group) (value : (system.stage index).carrier),
      inclusion index (system.action index sigma value) =
        limitAction sigma (inclusion index value)

end SourceFilteredIndTopologicalMonoidAction

set_option synthInstance.maxHeartbeats 200000 in
-- The iterated scalar actions `Q_p -> K_v -> E` require deeper typeclass search.
section

namespace SourceFinitePlaceReconstruction

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

/-- A finite Galois stage's nonzero integral elements as a packaged
topological monoid. -/
noncomputable def stageIntegralPresentation
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    TopologicalMonoidPresentation.{u} where
  carrier := StageIntegralMonoid place stage
  monoid := inferInstance
  topology := inferInstance
  continuousMul := inferInstance

/-- Inclusion of nonzero integral elements along an inclusion of finite
Galois stages. -/
noncomputable def stageIntegralTransition
    (place : NumberField.FinitePlace K) {source target : StageIndex place}
    (map : source ≤ target) :
    ContinuousMonoidHom
      (stageIntegralPresentation place source)
      (stageIntegralPresentation place target) where
  hom :=
    { toFun := fun value =>
        ⟨transitionContinuousLinearMap place map value.1, by
          simpa only [transitionContinuousLinearMap,
            LinearMap.mkContinuous_apply, transitionLinearMap,
            LinearMap.coe_restrictScalars] using value.2⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro first second
        apply Subtype.ext
        rfl }
  continuous := by
    apply Continuous.subtype_mk
    exact
      (transitionContinuousLinearMap place map).continuous.comp
        continuous_subtype_val

@[simp]
theorem stageIntegralTransition_val
    (place : NumberField.FinitePlace K) {source target : StageIndex place}
    (map : source ≤ target) (value : StageIntegralMonoid place source) :
    (stageIntegralTransition place map value).1 =
      transitionContinuousLinearMap place map value.1 := rfl

theorem stageIntegralTransition_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    stageIntegralTransition place (show stage ≤ stage from le_rfl) =
      ContinuousMonoidHom.id (stageIntegralPresentation place stage) := by
  apply ContinuousMonoidHom.ext
  apply MonoidHom.ext
  intro value
  apply Subtype.ext
  rfl

theorem stageIntegralTransition_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    (stageIntegralTransition place firstSecond).comp
        (stageIntegralTransition place secondThird) =
      stageIntegralTransition place (firstSecond.trans secondThird) := by
  apply ContinuousMonoidHom.ext
  apply MonoidHom.ext
  intro value
  apply Subtype.ext
  rfl

/-- Restriction of a Krull automorphism to the nonzero integral elements of
one finite Galois stage. -/
noncomputable def stageGaloisIntegralMap
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : StageIntegralMonoid place stage) :
    StageIntegralMonoid place stage :=
  ⟨stageGaloisContinuousLinearEquiv place stage sigma value.1, by
    constructor
    · let algebraicInteger : SourceMLFAlgebraicIntegerRing (Base place) :=
        ⟨(value.1 : Closure place), value.2.1⟩
      have hintegral :=
        (SourceMLFIntegralMonoid.integralClosureAlgEquiv
          (Base place) sigma algebraicInteger).2
      simpa only [SourceMLFIntegralMonoid.integralClosureAlgEquiv,
        Subring.coe_map, AlgEquiv.coe_restrictScalars,
        stageGaloisContinuousLinearEquiv_coe] using hintegral
    · intro equality
      apply value.2.2
      apply sigma.injective
      rw [map_zero]
      exact
        (stageGaloisContinuousLinearEquiv_coe
          place stage sigma value.1).symm.trans
          equality⟩

@[simp]
theorem stageGaloisIntegralMap_val
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : StageIntegralMonoid place stage) :
    (stageGaloisIntegralMap place stage sigma value).1 =
      stageGaloisContinuousLinearEquiv place stage sigma value.1 := rfl

/-- A Krull automorphism as a multiplicative automorphism of one integral
stage. -/
noncomputable def stageGaloisIntegralMulAut
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (sigma : Closure place ≃ₐ[Base place] Closure place) :
    MulAut (StageIntegralMonoid place stage) where
  toFun := stageGaloisIntegralMap place stage sigma
  invFun := stageGaloisIntegralMap place stage sigma.symm
  left_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    change
      ((stageGaloisIntegralMap place stage sigma.symm
          (stageGaloisIntegralMap place stage sigma value)).1 :
        Closure place) = (value.1 : Closure place)
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    exact sigma.symm_apply_apply _
  right_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    change
      ((stageGaloisIntegralMap place stage sigma
          (stageGaloisIntegralMap place stage sigma.symm value)).1 :
        Closure place) = (value.1 : Closure place)
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    exact sigma.apply_symm_apply _
  map_mul' first second := by
    apply Subtype.ext
    apply Subtype.ext
    change
      ((stageGaloisIntegralMap place stage sigma (first * second)).1 :
          Closure place) =
        (((stageGaloisIntegralMap place stage sigma first).1 :
            Closure place) *
          ((stageGaloisIntegralMap place stage sigma second).1 :
            Closure place))
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    exact map_mul sigma _ _

/-- The absolute Galois group action on one integral finite stage. -/
noncomputable def stageGaloisIntegralAction
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    (Closure place ≃ₐ[Base place] Closure place) →*
      MulAut (StageIntegralMonoid place stage) where
  toFun := stageGaloisIntegralMulAut place stage
  map_one' := by
    apply MulEquiv.ext
    intro value
    apply Subtype.ext
    apply Subtype.ext
    change
      ((stageGaloisIntegralMap place stage 1 value).1 : Closure place) =
        (value.1 : Closure place)
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    rfl
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    apply Subtype.ext
    apply Subtype.ext
    change
      ((stageGaloisIntegralMap place stage (first * second) value).1 :
          Closure place) =
        ((stageGaloisIntegralMap place stage first
          (stageGaloisIntegralMap place stage second value)).1 :
            Closure place)
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    rw [stageGaloisIntegralMap_val]
    rw [stageGaloisContinuousLinearEquiv_coe]
    rfl

/-- The Krull action on every finite integral stage is jointly continuous. -/
theorem continuous_stageGaloisIntegralAction
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Continuous fun input :
        (Closure place ≃ₐ[Base place] Closure place) ×
          StageIntegralMonoid place stage =>
      stageGaloisIntegralAction place stage input.1 input.2 := by
  apply Continuous.subtype_mk
  let projection :
      (Closure place ≃ₐ[Base place] Closure place) ×
          StageIntegralMonoid place stage →
        (Closure place ≃ₐ[Base place] Closure place) × stage :=
    fun input => (input.1, input.2.1)
  have hprojection : Continuous projection :=
    continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hcontinuous :=
    (continuous_stageGaloisAction place stage).comp hprojection
  refine hcontinuous.congr ?_
  intro input
  rfl

/-- Finite-stage inclusions commute with the literal Krull actions. -/
theorem stageIntegralTransition_galois
    (place : NumberField.FinitePlace K) {source target : StageIndex place}
    (map : source ≤ target)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : StageIntegralMonoid place source) :
    stageIntegralTransition place map
        (stageGaloisIntegralAction place source sigma value) =
      stageGaloisIntegralAction place target sigma
        (stageIntegralTransition place map value) := by
  apply Subtype.ext
  apply Subtype.ext
  change
    ((stageGaloisIntegralMap place source sigma value).1 : Closure place) =
      ((stageGaloisIntegralMap place target sigma
        (stageIntegralTransition place map value)).1 : Closure place)
  rw [stageGaloisIntegralMap_val]
  rw [stageGaloisContinuousLinearEquiv_coe]
  rw [stageGaloisIntegralMap_val]
  rw [stageGaloisContinuousLinearEquiv_coe]
  rfl

/-- The canonical filtered ind-system of finite Galois integral monoids. -/
noncomputable def integralIndSystem
    (place : NumberField.FinitePlace K) :
    SourceFilteredIndTopologicalMonoidAction
      (Closure place ≃ₐ[Base place] Closure place) where
  Index := StageIndex place
  indexPreorder := inferInstance
  indexDirected first second :=
    ⟨first ⊔ second, le_sup_left, le_sup_right⟩
  stage := stageIntegralPresentation place
  transition := stageIntegralTransition place
  transition_refl := stageIntegralTransition_refl place
  transition_trans := stageIntegralTransition_trans place
  action := stageGaloisIntegralAction place
  continuous_action := continuous_stageGaloisIntegralAction place
  transition_equivariant := stageIntegralTransition_galois place

/-- The canonical monoid inclusion of one integral stage into the algebraic
limit carrier.  Its continuity was proved separately by
`continuous_stageIntegralToInd`. -/
noncomputable def stageIntegralToIndHom
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    StageIntegralMonoid place stage →* IndIntegralMonoid place :=
  stageIntegralToInd place stage

theorem stageIntegralToIndHom_injective
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    Function.Injective (stageIntegralToIndHom place stage) := by
  intro first second equality
  apply Subtype.ext
  apply Subtype.ext
  have hcarrier := congrArg
    (fun value : IndIntegralMonoid place =>
      carrierMulEquivAlgebraicClosure place value.1)
    equality
  change (first.1 : Closure place) = (second.1 : Closure place)
  change
    carrierMulEquivAlgebraicClosure place
        (stageToCarrier place stage first.1) =
      carrierMulEquivAlgebraicClosure place
        (stageToCarrier place stage second.1) at hcarrier
  simpa only [carrierMulEquiv_stageToCarrier] using hcarrier

/-- Stage inclusions into the algebraic limit commute with every transition. -/
theorem stageIntegralToIndHom_transition
    (place : NumberField.FinitePlace K) {source target : StageIndex place}
    (map : source ≤ target) :
    (stageIntegralToIndHom place target).comp
        (stageIntegralTransition place map).hom =
      stageIntegralToIndHom place source := by
  apply MonoidHom.ext
  intro value
  apply Subtype.ext
  apply (carrierMulEquivAlgebraicClosure place).injective
  change
    carrierMulEquivAlgebraicClosure place
        (stageToCarrier place target
          (stageIntegralTransition place map value).1) =
      carrierMulEquivAlgebraicClosure place
        (stageToCarrier place source value.1)
  rw [carrierMulEquiv_stageToCarrier]
  rw [carrierMulEquiv_stageToCarrier]
  rfl

/-- The stage action agrees with the algebraic action on the exhaustive limit. -/
theorem stageIntegralToIndHom_galois
    (place : NumberField.FinitePlace K) (stage : StageIndex place)
    (sigma : Closure place ≃ₐ[Base place] Closure place)
    (value : StageIntegralMonoid place stage) :
    stageIntegralToIndHom place stage
        (stageGaloisIntegralAction place stage sigma value) =
      indGaloisAction place sigma
        (stageIntegralToIndHom place stage value) := by
  apply Subtype.ext
  exact
    (indGaloisMulAut_stageIntegralToInd_val
      place stage sigma value).symm

/-- The canonical ind-system exhausts the literal nonzero integral monoid of
the algebraic closure, compatibly with the Krull action. -/
noncomputable def integralIndSystemLimit
    (place : NumberField.FinitePlace K) :
    (integralIndSystem place).ExhaustiveAlgebraicLimit where
  limit := IndIntegralMonoid place
  limitMonoid := inferInstance
  inclusion := stageIntegralToIndHom place
  inclusion_injective := stageIntegralToIndHom_injective place
  inclusion_transition := stageIntegralToIndHom_transition place
  exhausted := exists_stage_representation place
  limitAction := indGaloisAction place
  inclusion_equivariant := stageIntegralToIndHom_galois place

/-- A countable canonical stage category admits the positive-integer cofinal
presentation required by the paper's strict convention for `ind-`.  The
downstream source theorem proves this countability for number-field
completions. -/
noncomputable def integralIndSequentialPresentation
    (place : NumberField.FinitePlace K)
    [Countable (StageIndex place)] :
    (integralIndSystem place).SequentialCofinalPresentation where
  stageIndex :=
    CategoryTheory.Limits.IsFiltered.sequentialFunctor_obj
      (StageIndex place)
  monotone_stageIndex :=
    CategoryTheory.Limits.IsFiltered.sequentialFunctor_map
      (StageIndex place)
  cofinal_stageIndex :=
    CategoryTheory.Limits.IsFiltered.sequentialFunctor_final_aux
      (StageIndex place)

end

end SourceFinitePlaceReconstruction

end


end Iut
