/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageDivisorTransition
import Iut.Foundations.SourceModelFrobenioid
import Iut.Foundations.SourceModelFrobenioidPresentation
import Mathlib.CategoryTheory.Limits.IsConnected

/-!
# The finite-stage model Frobenioid input

The finite Galois reconstruction stages are organized in the opposite
direction, as required by the contravariant divisor functor.  This module
constructs the genuine sharp saturated divisor monoid (using a universe-lifted
copy of `Nat`), its ramification-weighted pullbacks, the additive group of
nonzero stage elements, and the model Frobenioid `Input`.

The divisor naturality field is proved from the normalized valuation transition
and the induced Grothendieck-group map.  No finite-stage transition, model
recognition, or Frobenioid axiom is supplied as an assumption.
-/

open CategoryTheory

namespace Iut.SourceFinitePlaceReconstruction

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

abbrev StageBase (place : NumberField.FinitePlace K) :=
  (StageIndex place)ᵒᵖ

abbrev StageFSM {place : NumberField.FinitePlace K}
    {source target : StageBase place} (arrow : source ⟶ target) : Prop :=
  IsIso arrow

theorem stageBase_eq_of_isIso
    {place : NumberField.FinitePlace K}
    {source target : StageBase place} (arrow : source ⟶ target)
    [IsIso arrow] : source = target := by
  exact Opposite.unop_injective
    (le_antisymm (inv arrow).unop.le arrow.unop.le)

abbrev StageDivisor := ULift.{u} ℕ

def stageDivisorEquivNat : StageDivisor.{u} ≃+ ℕ where
  toEquiv := Equiv.ulift
  map_add' _ _ := rfl

noncomputable def stageDivisorGrothendieckToInt :
    Algebra.GrothendieckAddGroup StageDivisor.{u} →+ ℤ :=
  Algebra.GrothendieckAddGroup.lift
    ((Int.ofNatHom : ℕ →+ ℤ).comp stageDivisorEquivNat.toAddMonoidHom)

noncomputable def intToStageDivisorGrothendieck :
    ℤ →+ Algebra.GrothendieckAddGroup StageDivisor.{u} :=
  zmultiplesHom (Algebra.GrothendieckAddGroup StageDivisor.{u})
    (Algebra.GrothendieckAddGroup.of (ULift.up 1))

@[simp]
theorem stageDivisorGrothendieckToInt_of (value : StageDivisor.{u}) :
    stageDivisorGrothendieckToInt
      (Algebra.GrothendieckAddGroup.of value) = value.down := by
  have equality :=
    (Algebra.GrothendieckAddGroup.lift
      (M := StageDivisor.{u}) (G := ℤ)).symm_apply_apply
        ((Int.ofNatHom : ℕ →+ ℤ).comp
          stageDivisorEquivNat.toAddMonoidHom)
  exact DFunLike.congr_fun equality value

@[simp]
theorem stageDivisor_nsmul_up (value : ℕ) :
    value • (ULift.up 1 : StageDivisor.{u}) = ULift.up value := by
  induction value with
  | zero => rfl
  | succ value ih =>
      rw [succ_nsmul, ih]
      rfl

@[simp]
theorem intToStageDivisorGrothendieck_ofNat (value : ℕ) :
    intToStageDivisorGrothendieck (value : ℤ) =
      Algebra.GrothendieckAddGroup.of (ULift.up value : StageDivisor.{u}) := by
  change (value : ℤ) • Algebra.GrothendieckAddGroup.of (ULift.up 1) =
    Algebra.GrothendieckAddGroup.of (ULift.up value)
  calc
    (value : ℤ) • Algebra.GrothendieckAddGroup.of
        (ULift.up 1 : StageDivisor.{u}) =
        value • Algebra.GrothendieckAddGroup.of
          (ULift.up 1 : StageDivisor.{u}) := by simp
    _ = Algebra.GrothendieckAddGroup.of
        (value • (ULift.up 1 : StageDivisor.{u})) := by
      symm
      exact map_nsmul
        (Algebra.GrothendieckAddGroup.of (M := StageDivisor.{u}))
        value (ULift.up 1)
    _ = Algebra.GrothendieckAddGroup.of
        (ULift.up value : StageDivisor.{u}) := by rw [stageDivisor_nsmul_up]

theorem stageDivisorGrothendieck_right_hom :
    (stageDivisorGrothendieckToInt.comp
        intToStageDivisorGrothendieck) =
      AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext_int
  change stageDivisorGrothendieckToInt
      (intToStageDivisorGrothendieck (1 : ℤ)) = 1
  calc
    stageDivisorGrothendieckToInt
        (intToStageDivisorGrothendieck (1 : ℤ)) =
        stageDivisorGrothendieckToInt
          (Algebra.GrothendieckAddGroup.of
            (ULift.up 1)) :=
      congrArg stageDivisorGrothendieckToInt
        (intToStageDivisorGrothendieck_ofNat 1)
    _ = 1 := by
      simpa using stageDivisorGrothendieckToInt_of
        (ULift.up 1)

theorem stageDivisorGrothendieck_left_hom :
    (intToStageDivisorGrothendieck.comp
        stageDivisorGrothendieckToInt) =
      AddMonoidHom.id
        (Algebra.GrothendieckAddGroup StageDivisor.{u}) := by
  apply (Algebra.GrothendieckAddGroup.lift
    (M := StageDivisor.{u})
    (G := Algebra.GrothendieckAddGroup StageDivisor.{u})).symm.injective
  apply AddMonoidHom.ext
  intro value
  change intToStageDivisorGrothendieck
      (stageDivisorGrothendieckToInt
        (Algebra.GrothendieckAddGroup.of value)) =
    Algebra.GrothendieckAddGroup.of value
  rw [stageDivisorGrothendieckToInt_of,
    intToStageDivisorGrothendieck_ofNat]

noncomputable def stageDivisorGrothendieckEquivInt :
    Algebra.GrothendieckAddGroup StageDivisor.{u} ≃+ ℤ :=
  { toFun := stageDivisorGrothendieckToInt
    invFun := intToStageDivisorGrothendieck
    left_inv := fun value =>
      DFunLike.congr_fun stageDivisorGrothendieck_left_hom value
    right_inv := fun value =>
      DFunLike.congr_fun stageDivisorGrothendieck_right_hom value
    map_add' := stageDivisorGrothendieckToInt.map_add }

@[simp]
theorem stageDivisorGrothendieckEquivInt_of (value : StageDivisor.{u}) :
    stageDivisorGrothendieckEquivInt
      (Algebra.GrothendieckAddGroup.of value) = value.down :=
  stageDivisorGrothendieckToInt_of value

noncomputable def stageDivisorialAddMonoid : DivisorialAddMonoid.{u} where
  carrier := StageDivisor.{u}
  integral := by
    intro first second third equality
    apply ULift.down_injective
    exact Nat.add_left_cancel (congrArg ULift.down equality)
  sharp := by
    intro value hypothesis
    apply ULift.down_injective
    exact Nat.isAddUnit_iff.mp
      (hypothesis.map stageDivisorEquivNat.toAddMonoidHom)
  saturated := by
    intro value multiple hypothesis
    obtain ⟨divisor, equality⟩ := hypothesis
    have mappedEquality :=
      congrArg stageDivisorGrothendieckEquivInt equality
    have mappedEquality' :
        multiple.1 • stageDivisorGrothendieckEquivInt value =
          (divisor.down : ℤ) := by
      simpa only [map_nsmul, stageDivisorGrothendieckEquivInt_of] using
        mappedEquality.symm
    have valueNonnegative :
        0 ≤ stageDivisorGrothendieckEquivInt value := by
      apply (nsmul_nonneg_iff (Nat.ne_of_gt multiple.2)).mp
      rw [mappedEquality']
      exact Int.natCast_nonneg divisor.down
    refine ⟨ULift.up (Int.toNat
      (stageDivisorGrothendieckEquivInt value)), ?_⟩
    apply stageDivisorGrothendieckEquivInt.injective
    rw [stageDivisorGrothendieckEquivInt_of]
    exact Int.toNat_of_nonneg valueNonnegative

noncomputable def liftedStageDivisorPullback
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    StageDivisor.{u} →+ StageDivisor.{u} :=
  stageDivisorEquivNat.symm.toAddMonoidHom.comp
    ((stageDivisorPullback place map).comp
      stageDivisorEquivNat.toAddMonoidHom)

theorem liftedStageDivisorPullback_refl
    (place : NumberField.FinitePlace K) (stage : StageIndex place) :
    liftedStageDivisorPullback place (show stage ≤ stage from le_rfl) =
      AddMonoidHom.id StageDivisor.{u} := by
  apply AddMonoidHom.ext
  intro value
  apply ULift.down_injective
  change stageDivisorPullback place le_rfl value.down = value.down
  simpa using DFunLike.congr_fun
    (stageDivisorPullback_refl place stage) value.down

theorem liftedStageDivisorPullback_trans
    (place : NumberField.FinitePlace K)
    {first second third : StageIndex place}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    liftedStageDivisorPullback place (firstSecond.trans secondThird) =
      (liftedStageDivisorPullback place secondThird).comp
        (liftedStageDivisorPullback place firstSecond) := by
  apply AddMonoidHom.ext
  intro value
  apply ULift.down_injective
  exact DFunLike.congr_fun
    (stageDivisorPullback_trans place firstSecond secondThird) value.down

theorem liftedStageDivisorPullback_injective
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target) :
    Function.Injective (liftedStageDivisorPullback place map) := by
  intro first second equality
  apply ULift.down_injective
  apply stageDivisorPullback_injective place map
  exact congrArg ULift.down equality

noncomputable def stageDivisorialMonoidOn
    (place : NumberField.FinitePlace K) :
    DivisorialMonoidOn (StageBase place) (@StageFSM K _ _ place) where
  obj _ := stageDivisorialAddMonoid
  pullback arrow := by
    change StageDivisor.{u} →+ StageDivisor.{u}
    exact liftedStageDivisorPullback place arrow.unop.le
  pullback_id object := by
    change liftedStageDivisorPullback place le_rfl =
      AddMonoidHom.id StageDivisor.{u}
    simpa using liftedStageDivisorPullback_refl place object.unop
  pullback_comp first second := by
    change liftedStageDivisorPullback place _ =
      (liftedStageDivisorPullback place _).comp
        (liftedStageDivisorPullback place _)
    simpa using liftedStageDivisorPullback_trans place
      second.unop.le first.unop.le
  characteristicallyInjective arrow :=
    liftedStageDivisorPullback_injective place arrow.unop.le
  fsmPullbackIsIso := by
    intro source target arrow arrowIsIso
    letI : IsIso arrow := arrowIsIso
    have object_eq : source = target := stageBase_eq_of_isIso arrow
    subst target
    have arrow_eq : arrow = 𝟙 source := Subsingleton.elim _ _
    rw [arrow_eq]
    have pullback_eq := liftedStageDivisorPullback_refl place source.unop
    rw [pullback_eq]
    exact Function.bijective_id

noncomputable def stageRationalFunctions
    (place : NumberField.FinitePlace K) :
    SourceModelFrobenioid.GroupLikeAddMonoidOn
      (StageBase place) (@StageFSM K _ _ place) where
  obj stage := Additive stage.unopˣ
  addCommGroup _ := inferInstance
  pullback arrow := (stageUnitTransition place arrow.unop.le).toAdditive
  pullback_id object := by
    simpa using congrArg MonoidHom.toAdditive
      (stageUnitTransition_refl place object.unop)
  pullback_comp first second := by
    apply AddMonoidHom.ext
    intro value
    change Additive.ofMul
        (stageUnitTransition place first.unop.le
          (stageUnitTransition place second.unop.le value.toMul)) =
      Additive.ofMul
        (stageUnitTransition place
          (second.unop.le.trans first.unop.le) value.toMul)
    exact congrArg Additive.ofMul
      (DFunLike.congr_fun
        (stageUnitTransition_trans place second.unop.le first.unop.le)
        value.toMul)
  pullback_injective arrow :=
    stageUnitTransition_injective place arrow.unop.le
  fsmPullbackIsIso := by
    intro source target arrow arrowIsIso
    letI : IsIso arrow := arrowIsIso
    have object_eq : source = target := stageBase_eq_of_isIso arrow
    subst target
    have arrow_eq : arrow = 𝟙 source := Subsingleton.elim _ _
    rw [arrow_eq]
    have pullback_eq := stageUnitTransition_refl place source.unop
    rw [pullback_eq]
    exact Function.bijective_id

noncomputable def stageModelDivisor
    (place : NumberField.FinitePlace K) (stage : StageBase place) :
    (stageRationalFunctions place).obj stage →+
      Algebra.GrothendieckAddGroup
        ((stageDivisorialMonoidOn place).obj stage).carrier :=
  intToStageDivisorGrothendieck.comp
    (stageNormalizedAdditiveValuation place stage.unop)

theorem stageDivisorGrothendieckPullback_apply
    (place : NumberField.FinitePlace K)
    {source target : StageBase place} (arrow : source ⟶ target)
    (exponent : ℤ) :
    (stageDivisorialMonoidOn place).gpPullback arrow
        (intToStageDivisorGrothendieck exponent) =
      intToStageDivisorGrothendieck
        (stageNormalizedAdditiveTransition place arrow.unop.le exponent) := by
  let map := arrow.unop.le
  have pullback_one :
      liftedStageDivisorPullback place map (ULift.up 1) =
        ULift.up (stageRamificationIndex place map) := by
    apply ULift.down_injective
    change stageDivisorPullback place map 1 =
      stageRamificationIndex place map
    simp [stageDivisorPullback]
  have exponent_one :
      stageNormalizedAdditiveTransition place map 1 =
        (stageRamificationIndex place map : ℤ) := by
    exact (stageNormalizedAdditiveTransition_eq_ramification_mul
      place map 1).trans (by simp)
  have homEquality :
      ((stageDivisorialMonoidOn place).gpPullback arrow).comp
          intToStageDivisorGrothendieck =
        intToStageDivisorGrothendieck.comp
          (stageNormalizedAdditiveTransition place map) := by
    apply AddMonoidHom.ext_int
    change
      (stageDivisorialMonoidOn place).gpPullback arrow
          (intToStageDivisorGrothendieck (1 : ℤ)) =
        intToStageDivisorGrothendieck
          (stageNormalizedAdditiveTransition place map 1)
    calc
      (stageDivisorialMonoidOn place).gpPullback arrow
          (intToStageDivisorGrothendieck (1 : ℤ)) =
          (stageDivisorialMonoidOn place).gpPullback arrow
            (Algebra.GrothendieckAddGroup.of
              (ULift.up 1 : StageDivisor.{u})) := by
        congr 1
        exact intToStageDivisorGrothendieck_ofNat 1
      _ = Algebra.GrothendieckAddGroup.of
            (liftedStageDivisorPullback place map
              (ULift.up 1)) := by
        rw [DivisorialMonoidOn.gpPullback_of]
        change Algebra.GrothendieckAddGroup.of
            (liftedStageDivisorPullback place map
              (ULift.up 1)) = _
        rfl
      _ = Algebra.GrothendieckAddGroup.of
            (ULift.up (stageRamificationIndex place map)) := by
        rw [pullback_one]
      _ = intToStageDivisorGrothendieck
            (stageNormalizedAdditiveTransition place map 1) := by
        rw [exponent_one, intToStageDivisorGrothendieck_ofNat]
  exact DFunLike.congr_fun homEquality exponent

noncomputable def stageModelInput
    (place : NumberField.FinitePlace K) :
    SourceModelFrobenioid.Input (stageDivisorialMonoidOn place) where
  rationalFunctions := stageRationalFunctions place
  divisor := stageModelDivisor place
  divisor_natural := by
    intro source target arrow value
    change
      intToStageDivisorGrothendieck
          (stageNormalizedAdditiveValuation place source.unop
            (Additive.ofMul
              (stageUnitTransition place arrow.unop.le value.toMul))) =
        (stageDivisorialMonoidOn place).gpPullback arrow
          (intToStageDivisorGrothendieck
            (stageNormalizedAdditiveValuation place target.unop
              value))
    rw [stageNormalizedAdditiveValuation_transition]
    rw [stageDivisorGrothendieckPullback_apply]
    rfl

noncomputable def stageBaseTerminal
    (place : NumberField.FinitePlace K) :
    CategoryTheory.Limits.IsTerminal
      (Opposite.op (⊥ : StageIndex place)) :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (Y := Opposite.op (⊥ : StageIndex place))
    (fun _stage =>
      (CategoryTheory.homOfLE
        (bot_le : (⊥ : StageIndex place) ≤ _stage.unop)).op)
    (fun _stage _arrow => Subsingleton.elim _ _)

theorem stageBase_isConnected
    (place : NumberField.FinitePlace K) :
    CategoryTheory.IsConnected (StageBase place) :=
  CategoryTheory.isConnected_of_isTerminal (StageBase place)
    (x := Opposite.op (⊥ : StageIndex place))
    (stageBaseTerminal place)

noncomputable instance stageBase_isConnected_inst
    (place : NumberField.FinitePlace K) :
    CategoryTheory.IsConnected (StageBase place) :=
  stageBase_isConnected place

theorem stageBase_arrow_epi
    (place : NumberField.FinitePlace K)
    {source target : StageBase place} (arrow : source ⟶ target) :
    Epi arrow := by
  infer_instance

noncomputable def stageModelPreFrobenioidPresentation
    (place : NumberField.FinitePlace K) :
    PreFrobenioidPresentation := by
  letI : CategoryTheory.IsConnected (StageBase place) :=
    stageBase_isConnected place
  exact SourceModelFrobenioid.Carrier.preFrobenioidPresentation
    (stageDivisorialMonoidOn place) (stageModelInput place)
    (fun {source target} arrow => stageBase_arrow_epi place arrow)

noncomputable def stageModelFrobenioidPresentation
    (place : NumberField.FinitePlace K) :
    FrobenioidPresentation := by
  letI : CategoryTheory.IsConnected (StageBase place) :=
    stageBase_isConnected place
  exact SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := stageDivisorialMonoidOn place) (data := stageModelInput place)
    (fun {source target} arrow => stageBase_arrow_epi place arrow)

end

end Iut.SourceFinitePlaceReconstruction
