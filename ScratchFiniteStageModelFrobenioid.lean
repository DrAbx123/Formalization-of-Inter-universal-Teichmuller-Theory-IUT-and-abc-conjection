import Iut.Foundations.SourceFiniteStageDivisorTransition
import Iut.Foundations.SourceModelFrobenioidIntegralNaturality

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
theorem intToStageDivisorGrothendieck_ofNat (value : ℕ) :
    intToStageDivisorGrothendieck (value : ℤ) =
      Algebra.GrothendieckAddGroup.of (ULift.up value : StageDivisor.{u}) := by
  change (value : ℤ) • Algebra.GrothendieckAddGroup.of (ULift.up 1) =
    Algebra.GrothendieckAddGroup.of (ULift.up value)
  simp [← map_nsmul]

theorem stageDivisorGrothendieck_right_hom :
    (stageDivisorGrothendieckToInt.comp
        (intToStageDivisorGrothendieck (u := u))) =
      AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext_int
  simp [intToStageDivisorGrothendieck_ofNat]

theorem stageDivisorGrothendieck_left_hom :
    ((intToStageDivisorGrothendieck (u := u)).comp
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
  rfl

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
  obj _ := naturalDivisorialAddMonoid
  pullback arrow := liftedStageDivisorPullback place arrow.unop.le
  pullback_id object := by
    simpa using liftedStageDivisorPullback_refl place object.unop
  pullback_comp first second := by
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
    simpa using (congrArg MonoidHom.toAdditive
      (stageUnitTransition_trans place second.unop.le first.unop.le)).symm
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

end

end Iut.SourceFinitePlaceReconstruction
