/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidColimitStructure

/-!
# Morphism dictionary for the model birationalization

Frobenioids I, Proposition 4.4(iv) identifies the morphism classes before and
after birationalization.  This file proves the core zero-divisor clauses for
the concrete model target, transports them to the actual Hom-colimit category,
and proves the corresponding iff statements for the canonical localization.

All morphism and object clauses of Proposition 4.4(iv), including the exact
base-identity roof classification, are proved for the model target.
-/

open CategoryTheory CategoryTheory.Limits

namespace Iut.SourceModelFrobenioid

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

namespace BirationalObject

/-- Two concrete pullback-comparison targets agree on their two data fields. -/
theorem pullbackComparisonTarget_ext
    {source target test : BirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target}
    {left right :
      (preFrobenioid (Phi := Phi) (data := data)).PullbackComparisonTarget
        arrow test}
    (toCodomain : left.toCodomain = right.toCodomain)
    (toBaseDomain : left.toBaseDomain = right.toBaseDomain) :
    left = right := by
  cases left
  cases right
  cases toCodomain
  cases toBaseDomain
  rfl

/-- Every arrow in the zero-divisor target is an isometry. -/
theorem isIsometric
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsometric arrow := by
  change (default : PUnit) = 0
  rfl

/-- A linear concrete target arrow realizes the representable pullback square. -/
theorem isPullback_of_isLinear
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target)
    (linear : (preFrobenioid (Phi := Phi) (data := data)).IsLinear arrow) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPullback arrow := by
  change arrow.frobeniusDegree = 1 at linear
  intro test
  constructor
  · intro left right equality
    have compositeEquality : left ≫ arrow = right ≫ arrow :=
      congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain equality
    have baseEquality : left.base = right.base :=
      congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain equality
    apply BirationalHom.ext
    · have projected := congrArg BirationalHom.frobeniusDegree compositeEquality
      change left.frobeniusDegree * arrow.frobeniusDegree =
        right.frobeniusDegree * arrow.frobeniusDegree at projected
      rw [linear] at projected
      simpa using projected
    · exact baseEquality
    · have projected := congrArg BirationalHom.rationalFunction compositeEquality
      change data.rationalFunctions.pullback left.base arrow.rationalFunction +
          arrow.frobeniusDegree.val • left.rationalFunction =
        data.rationalFunctions.pullback right.base arrow.rationalFunction +
          arrow.frobeniusDegree.val • right.rationalFunction at projected
      rw [linear, baseEquality] at projected
      simp only [PNat.val_ofNat, one_nsmul] at projected
      exact add_left_cancel projected
  · intro comparison
    let lift : test ⟶ source :=
      { frobeniusDegree := comparison.toCodomain.frobeniusDegree
        base := comparison.toBaseDomain
        rationalFunction := comparison.toCodomain.rationalFunction -
          data.rationalFunctions.pullback
            (show Object.base test.underlying ⟶
              Object.base source.underlying from comparison.toBaseDomain)
            arrow.rationalFunction }
    refine ⟨lift, ?_⟩
    cases comparison with
    | mk toCodomain toBaseDomain commutes =>
      dsimp only [PreFrobenioid.pullbackComparison]
      congr 1
      apply BirationalHom.ext
      · change toCodomain.frobeniusDegree * arrow.frobeniusDegree =
          toCodomain.frobeniusDegree
        rw [linear]
        simp
      · exact commutes.symm
      · change data.rationalFunctions.pullback
              (show Object.base test.underlying ⟶
                Object.base source.underlying from toBaseDomain)
              arrow.rationalFunction +
            arrow.frobeniusDegree.val •
              (toCodomain.rationalFunction -
                data.rationalFunctions.pullback
                  (show Object.base test.underlying ⟶
                    Object.base source.underlying from toBaseDomain)
                  arrow.rationalFunction) =
          toCodomain.rationalFunction
        rw [linear]
        simp only [PNat.val_ofNat, one_nsmul]
        abel

/-- The representable pullback property forces concrete Frobenius degree one. -/
theorem isLinear_of_isPullback
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target)
    (pullback : (preFrobenioid (Phi := Phi) (data := data)).IsPullback arrow) :
    (preFrobenioid (Phi := Phi) (data := data)).IsLinear arrow := by
  let degreeOneArrow : source ⟶ target :=
    { frobeniusDegree := 1
      base := arrow.base
      rationalFunction := 0 }
  let comparison :
      (preFrobenioid (Phi := Phi) (data := data)).PullbackComparisonTarget
        arrow source :=
    { toCodomain := degreeOneArrow
      toBaseDomain := 𝟙 _
      commutes := by
        change arrow.base = 𝟙 _ ≫ arrow.base
        simp }
  obtain ⟨lift, equality⟩ := (pullback source).2 comparison
  have compositeEquality :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain equality
  have projected := congrArg BirationalHom.frobeniusDegree compositeEquality
  change lift.frobeniusDegree * arrow.frobeniusDegree = 1 at projected
  change arrow.frobeniusDegree = 1
  apply PNat.eq
  have projectedVal := congrArg PNat.val projected
  change lift.frobeniusDegree.val * arrow.frobeniusDegree.val = 1 at projectedVal
  exact Nat.eq_one_of_mul_eq_one_left projectedVal

/-- Proposition 4.4(iv): concrete pullback arrows are exactly linear arrows. -/
theorem isPullback_iff_isLinear
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPullback arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsLinear arrow :=
  ⟨isLinear_of_isPullback arrow, isPullback_of_isLinear arrow⟩

/-- A pre-step in the concrete target is an isomorphism. -/
theorem isIso_of_isPreStep
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target)
    (preStep : (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow) :
    IsIso arrow := by
  exact (isoOfLinearBaseIso arrow preStep.1 preStep.2).isIso_hom

/-- An isomorphism in the concrete target has degree one and invertible base. -/
theorem isPreStep_of_isIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (arrowIsIso : IsIso arrow) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow := by
  letI : IsIso arrow := arrowIsIso
  constructor
  · change arrow.frobeniusDegree = 1
    have identity := congrArg BirationalHom.frobeniusDegree
      (IsIso.hom_inv_id arrow)
    change arrow.frobeniusDegree * (inv arrow).frobeniusDegree = 1 at identity
    apply PNat.eq
    have valueIdentity := congrArg PNat.val identity
    exact Nat.eq_one_of_dvd_one ⟨(inv arrow).frobeniusDegree.val,
      valueIdentity.symm⟩
  · change IsIso
      ((preFrobenioid (Phi := Phi) (data := data)).base.map arrow)
    infer_instance

/-- Proposition 4.4(iv): target isomorphisms are precisely target pre-steps. -/
theorem isIso_iff_isPreStep
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    IsIso arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow :=
  ⟨isPreStep_of_isIso arrow, isIso_of_isPreStep arrow⟩

/-- Every object of the concrete group-like target is isotropic. -/
theorem isIsotropic
    (object : BirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsotropic object := by
  intro target arrow preStep _
  exact isIso_of_isPreStep arrow preStep

/-- Every arrow in the group-like target is co-angular. -/
theorem isCoAngular
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsCoAngular arrow := by
  intro firstObject secondObject gamma beta alpha _ _ betaPreStep _ _
  exact isIso_of_isPreStep beta betaPreStep

/-- Every arrow in the group-like target is LB-invertible. -/
theorem isLBInvertible
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsLBInvertible arrow :=
  ⟨isCoAngular arrow, isIsometric arrow⟩

/-- In the group-like target, Frobenius type means base-isomorphism. -/
theorem isOfFrobeniusType_iff_isBaseIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsOfFrobeniusType arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsBaseIso arrow := by
  constructor
  · exact fun hypothesis ↦ hypothesis.2
  · exact fun hypothesis ↦ ⟨isLBInvertible arrow, hypothesis⟩

end BirationalObject

namespace Carrier.ColimitBirationalObject

/-- Two colimit pullback-comparison targets agree on their two data fields. -/
theorem pullbackComparisonTarget_ext
    {source target test : ColimitBirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target}
    {left right :
      (preFrobenioid (Phi := Phi) (data := data)).PullbackComparisonTarget
        arrow test}
    (toCodomain : left.toCodomain = right.toCodomain)
    (toBaseDomain : left.toBaseDomain = right.toBaseDomain) :
    left = right := by
  cases left
  cases right
  cases toCodomain
  cases toBaseDomain
  rfl

/-- Every arrow in the Hom-colimit target is an isometry. -/
theorem isIsometric
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsometric arrow := by
  change (default : PUnit) = 0
  rfl

/-- Fully faithful comparison transports concrete pullback bijectivity. -/
theorem isPullback_of_isLinear
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target)
    (linear : (preFrobenioid (Phi := Phi) (data := data)).IsLinear arrow) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPullback arrow := by
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  let fullyFaithful :=
    comparisonFunctor_fullyFaithful (Phi := Phi) (data := data)
  have concreteLinear :
      (BirationalObject.preFrobenioid (Phi := Phi) (data := data)).IsLinear
        (comparison.map arrow) := linear
  have concretePullback := BirationalObject.isPullback_of_isLinear
    (comparison.map arrow) concreteLinear
  intro test
  constructor
  · intro left right equality
    apply comparison.map_injective
    apply (concretePullback (comparison.obj test)).1
    apply BirationalObject.pullbackComparisonTarget_ext
    · have compositeEquality : left ≫ arrow = right ≫ arrow :=
        congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain equality
      dsimp only [PreFrobenioid.pullbackComparison]
      rw [← comparison.map_comp, ← comparison.map_comp]
      exact congrArg (fun value ↦ comparison.map value) compositeEquality
    · dsimp only [PreFrobenioid.pullbackComparison]
      exact congrArg
        PreFrobenioid.PullbackComparisonTarget.toBaseDomain equality
  · intro value
    let concreteValue :
        (BirationalObject.preFrobenioid (Phi := Phi) (data := data)).PullbackComparisonTarget
          (comparison.map arrow) (comparison.obj test) :=
      { toCodomain := comparison.map value.toCodomain
        toBaseDomain := value.toBaseDomain
        commutes := by
          change (comparison.map value.toCodomain).base =
            value.toBaseDomain ≫ (comparison.map arrow).base
          exact value.commutes }
    obtain ⟨concreteLift, concreteEquality⟩ :=
      (concretePullback (comparison.obj test)).2 concreteValue
    let lift : test ⟶ source := fullyFaithful.preimage concreteLift
    have mappedLift : comparison.map lift = concreteLift :=
      fullyFaithful.map_preimage concreteLift
    refine ⟨lift, ?_⟩
    apply pullbackComparisonTarget_ext
    · apply comparison.map_injective
      dsimp only [PreFrobenioid.pullbackComparison]
      rw [comparison.map_comp, mappedLift]
      exact congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
        concreteEquality
    · dsimp only [PreFrobenioid.pullbackComparison]
      change (comparison.map lift).base = value.toBaseDomain
      rw [mappedLift]
      exact congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain
        concreteEquality

/-- Pullback surjectivity forces degree one in the Hom-colimit target. -/
theorem isLinear_of_isPullback
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target)
    (pullback : (preFrobenioid (Phi := Phi) (data := data)).IsPullback arrow) :
    (preFrobenioid (Phi := Phi) (data := data)).IsLinear arrow := by
  let comparisonFunctor := comparisonFunctor (Phi := Phi) (data := data)
  let fullyFaithful :=
    comparisonFunctor_fullyFaithful (Phi := Phi) (data := data)
  let concreteDegreeOne :
      comparisonFunctor.obj source ⟶ comparisonFunctor.obj target :=
    { frobeniusDegree := 1
      base := (comparisonFunctor.map arrow).base
      rationalFunction := 0 }
  let degreeOneArrow : source ⟶ target :=
    fullyFaithful.preimage concreteDegreeOne
  have mappedDegreeOne :
      comparisonFunctor.map degreeOneArrow = concreteDegreeOne :=
    fullyFaithful.map_preimage concreteDegreeOne
  have degreeOneBase :
      (preFrobenioid (Phi := Phi) (data := data)).base.map degreeOneArrow =
        (preFrobenioid (Phi := Phi) (data := data)).base.map arrow := by
    change (comparisonFunctor.map degreeOneArrow).base =
      (comparisonFunctor.map arrow).base
    rw [mappedDegreeOne]
  let value :
      (preFrobenioid (Phi := Phi) (data := data)).PullbackComparisonTarget
        arrow source :=
    { toCodomain := degreeOneArrow
      toBaseDomain := 𝟙 _
      commutes := by
        rw [degreeOneBase]
        simp }
  obtain ⟨lift, equality⟩ := (pullback source).2 value
  have compositeEquality : lift ≫ arrow = degreeOneArrow :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain equality
  have mappedComposite :
      comparisonFunctor.map lift ≫ comparisonFunctor.map arrow =
        concreteDegreeOne := by
    rw [← comparisonFunctor.map_comp, compositeEquality, mappedDegreeOne]
  have projected := congrArg BirationalHom.frobeniusDegree mappedComposite
  change (comparisonFunctor.map lift).frobeniusDegree *
      (comparisonFunctor.map arrow).frobeniusDegree = 1 at projected
  change (comparisonFunctor.map arrow).frobeniusDegree = 1
  apply PNat.eq
  have projectedVal := congrArg PNat.val projected
  change (comparisonFunctor.map lift).frobeniusDegree.val *
      (comparisonFunctor.map arrow).frobeniusDegree.val = 1 at projectedVal
  exact Nat.eq_one_of_mul_eq_one_left projectedVal

/-- Proposition 4.4(iv): colimit pullback arrows are exactly linear arrows. -/
theorem isPullback_iff_isLinear
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPullback arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsLinear arrow :=
  ⟨isLinear_of_isPullback arrow, isPullback_of_isLinear arrow⟩

/-- Cancelling a roof denominator on the base recovers the numerator base. -/
theorem denominator_base_comp_roofValue_base
    {source target : Carrier Phi data}
    (denominator : Carrier.CoAngularPreStepOver source)
    (numerator : denominator.source ⟶ target) :
    denominator.hom.base ≫
        (Carrier.CoAngularPreStepOver.roofValue denominator numerator).base =
      numerator.base := by
  have cancellation :=
    Carrier.CoAngularPreStepOver.map_denominator_comp_roofValue
      denominator numerator
  exact congrArg BirationalHom.base cancellation

/-- The exact source roof data classifying a base-identity endomorphism. -/
structure BaseIdentityRoof
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (arrow : object ⟶ object) where
  denominator : Carrier.CoAngularPreStepOver object.underlying
  numerator : denominator.source ⟶ object.underlying
  baseEquivalent : numerator.base = denominator.hom.base
  represents :
    colimit.ι
        (Carrier.CoAngularPreStepOver.homDiagram
          object.underlying object.underlying)
        (Opposite.op denominator) numerator = arrow

/-- A base-identity colimit endomorphism has a base-equivalent source roof. -/
theorem baseIdentityRoof_of_isBaseIdentity
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : object ⟶ object)
    (baseIdentity :
      (preFrobenioid (Phi := Phi) (data := data)).IsBaseIdentity arrow) :
    Nonempty (BaseIdentityRoof object arrow) := by
  rcases Limits.Types.jointly_surjective' arrow with
    ⟨index, numerator, represents⟩
  let denominator := index.unop
  have roofBaseIdentity :
      (Carrier.CoAngularPreStepOver.roofValue denominator numerator).base =
        𝟙 (Object.base object.underlying) := by
    change
      (Carrier.CoAngularPreStepOver.colimitComparisonEquiv
        object.underlying object.underlying arrow).base = 𝟙 _ at baseIdentity
    rw [← represents,
      Carrier.CoAngularPreStepOver.colimitComparisonEquiv_iota] at baseIdentity
    exact baseIdentity
  have baseEquivalent : numerator.base = denominator.hom.base := by
    have cancellation :=
      denominator_base_comp_roofValue_base denominator numerator
    rw [roofBaseIdentity] at cancellation
    have denominatorEqNumerator : denominator.hom.base = numerator.base :=
      Eq.trans (Category.comp_id denominator.hom.base).symm cancellation
    exact denominatorEqNumerator.symm
  exact ⟨
    { denominator := denominator
      numerator := numerator
      baseEquivalent := baseEquivalent
      represents := represents }⟩

/-- A roof with base-equivalent numerator and denominator is base-identity. -/
theorem isBaseIdentity_of_baseIdentityRoof
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    {arrow : object ⟶ object} (roof : BaseIdentityRoof object arrow) :
    (preFrobenioid (Phi := Phi) (data := data)).IsBaseIdentity arrow := by
  have denominatorBaseIsIso := roof.denominator.preStep.2
  change IsIso roof.denominator.hom.base at denominatorBaseIsIso
  letI : IsIso roof.denominator.hom.base := denominatorBaseIsIso
  change
    (Carrier.CoAngularPreStepOver.colimitComparisonEquiv
      object.underlying object.underlying arrow).base = 𝟙 _
  rw [← roof.represents,
    Carrier.CoAngularPreStepOver.colimitComparisonEquiv_iota]
  apply (cancel_epi roof.denominator.hom.base).1
  calc
    roof.denominator.hom.base ≫
        (Carrier.CoAngularPreStepOver.roofValue
          roof.denominator roof.numerator).base =
      roof.numerator.base :=
        denominator_base_comp_roofValue_base
          roof.denominator roof.numerator
    _ = roof.denominator.hom.base := roof.baseEquivalent
    _ = roof.denominator.hom.base ≫ 𝟙 _ := (Category.comp_id _).symm

/-- Proposition 4.4(iv)'s base-identity endomorphism roof classification. -/
theorem isBaseIdentity_iff_nonempty_baseIdentityRoof
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : object ⟶ object) :
    (preFrobenioid (Phi := Phi) (data := data)).IsBaseIdentity arrow ↔
      Nonempty (BaseIdentityRoof object arrow) :=
  ⟨baseIdentityRoof_of_isBaseIdentity arrow,
    fun ⟨roof⟩ ↦ isBaseIdentity_of_baseIdentityRoof roof⟩

/-- The comparison preserves and reflects the pre-step predicate definitionally. -/
theorem isPreStep_iff_comparisonMap
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow ↔
      (BirationalObject.preFrobenioid (Phi := Phi) (data := data)).IsPreStep
        ((comparisonFunctor (Phi := Phi) (data := data)).map arrow) :=
  Iff.rfl

/-- Proposition 4.4(iv): colimit isomorphisms are precisely pre-steps. -/
theorem isIso_iff_isPreStep
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    IsIso arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsPreStep arrow := by
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  constructor
  · intro arrowIsIso
    letI : IsIso arrow := arrowIsIso
    exact (isPreStep_iff_comparisonMap arrow).2
      (BirationalObject.isPreStep_of_isIso (comparison.map arrow)
        (inferInstance : IsIso (comparison.map arrow)))
  · intro preStep
    haveI : IsIso (comparison.map arrow) :=
      BirationalObject.isIso_of_isPreStep (comparison.map arrow)
        ((isPreStep_iff_comparisonMap arrow).1 preStep)
    exact isIso_of_reflects_iso arrow comparison

/-- Every object of the Hom-colimit group-like target is isotropic. -/
theorem isIsotropic
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsotropic object := by
  intro target arrow preStep _
  exact (isIso_iff_isPreStep arrow).2 preStep

/-- Every arrow in the Hom-colimit group-like target is co-angular. -/
theorem isCoAngular
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsCoAngular arrow := by
  intro firstObject secondObject gamma beta alpha _ _ betaPreStep _ _
  exact (isIso_iff_isPreStep beta).2 betaPreStep

/-- Every arrow in the Hom-colimit target is LB-invertible. -/
theorem isLBInvertible
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsLBInvertible arrow :=
  ⟨isCoAngular arrow, isIsometric arrow⟩

/-- In the Hom-colimit target, Frobenius type means base-isomorphism. -/
theorem isOfFrobeniusType_iff_isBaseIso
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsOfFrobeniusType arrow ↔
      (preFrobenioid (Phi := Phi) (data := data)).IsBaseIso arrow := by
  constructor
  · exact fun hypothesis ↦ hypothesis.2
  · exact fun hypothesis ↦ ⟨isLBInvertible arrow, hypothesis⟩

/-- A source arrow becomes invertible exactly when it is a source pre-step. -/
theorem localization_map_isIso_iff_isPreStep
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    IsIso ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsPreStep arrow := by
  constructor
  · intro mappedIsIso
    let localization := localizationFunctor (Phi := Phi) (data := data)
    let comparison := comparisonFunctor (Phi := Phi) (data := data)
    letI : IsIso (localization.map arrow) := mappedIsIso
    have comparisonIsIso :
        IsIso (comparison.map (localization.map arrow)) := inferInstance
    have concreteIsIso : IsIso
        ((BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
          arrow) := by
      rw [comparisonFunctor_map_localizationFunctor] at comparisonIsIso
      exact comparisonIsIso
    exact BirationalObject.isPreStep_of_isIso
      ((BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
        arrow) concreteIsIso
  · exact localizationFunctor_map_isIso_of_preStep arrow

/-- Proposition 4.4(iv)'s exact source characterization of target isomorphisms. -/
theorem localization_map_isIso_iff_coAngularPreStep
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    IsIso ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsPreStep arrow ∧
        (Carrier.preFrobenioid Phi data).IsCoAngular arrow := by
  rw [localization_map_isIso_iff_isPreStep]
  constructor
  · exact fun preStep ↦ ⟨preStep, Carrier.isCoAngular Phi data arrow⟩
  · exact fun hypothesis ↦ hypothesis.1

/-- The canonical functor preserves and reflects the base-isomorphism class. -/
theorem localization_map_isBaseIso_iff_isBaseIso
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsBaseIso
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsBaseIso arrow := by
  have mappedEquality := comparisonFunctor_map_localizationFunctor
    (Phi := Phi) (data := data) arrow
  have baseEquality := congrArg BirationalHom.base mappedEquality
  change IsIso
      ((comparisonFunctor (Phi := Phi) (data := data)).map
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow)).base ↔
    IsIso arrow.base
  rw [baseEquality]
  rfl

/-- The canonical functor preserves and reflects every fixed Frobenius degree. -/
theorem localization_map_frobeniusDegree_eq_iff
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (degree : ℕ+) :
    (preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) = degree ↔
      (Carrier.preFrobenioid Phi data).frobeniusDegree arrow = degree := by
  have mappedEquality := comparisonFunctor_map_localizationFunctor
    (Phi := Phi) (data := data) arrow
  have degreeEquality := congrArg BirationalHom.frobeniusDegree mappedEquality
  change
    ((comparisonFunctor (Phi := Phi) (data := data)).map
      ((localizationFunctor (Phi := Phi) (data := data)).map arrow)).frobeniusDegree =
        degree ↔
      arrow.frobeniusDegree = degree
  rw [degreeEquality]
  rfl

/-- Proposition 4.4(iv)'s exact source characterization of pullback arrows. -/
theorem localization_map_isPullback_iff
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPullback
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsCoAngular arrow ∧
        (Carrier.preFrobenioid Phi data).IsLinear arrow := by
  rw [isPullback_iff_isLinear]
  change
    (preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) = 1 ↔
      (Carrier.preFrobenioid Phi data).IsCoAngular arrow ∧
        (Carrier.preFrobenioid Phi data).IsLinear arrow
  rw [localization_map_frobeniusDegree_eq_iff arrow 1]
  constructor
  · exact fun linear ↦ ⟨Carrier.isCoAngular Phi data arrow, linear⟩
  · exact fun hypothesis ↦ hypothesis.2

/-- The source Frobenius-type clause becomes co-angular base-isomorphism. -/
theorem localization_map_isOfFrobeniusType_iff
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsOfFrobeniusType
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsCoAngular arrow ∧
        (Carrier.preFrobenioid Phi data).IsBaseIso arrow := by
  rw [isOfFrobeniusType_iff_isBaseIso,
    localization_map_isBaseIso_iff_isBaseIso]
  constructor
  · exact fun baseIso ↦ ⟨Carrier.isCoAngular Phi data arrow, baseIso⟩
  · exact fun hypothesis ↦ hypothesis.2

/-- Proposition 4.4(iv)'s pre-step iff for the canonical source functor. -/
theorem localization_map_isPreStep_iff_isPreStep
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsPreStep
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsPreStep arrow := by
  rw [← localization_map_isIso_iff_isPreStep arrow]
  exact (isIso_iff_isPreStep
    ((localizationFunctor (Phi := Phi) (data := data)).map arrow)).symm

/-- Proposition 4.4(iv)'s co-angular iff for the canonical source functor. -/
theorem localization_map_isCoAngular_iff_isCoAngular
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsCoAngular
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) ↔
      (Carrier.preFrobenioid Phi data).IsCoAngular arrow :=
  ⟨fun _ ↦ Carrier.isCoAngular Phi data arrow,
    fun _ ↦ isCoAngular
      ((localizationFunctor (Phi := Phi) (data := data)).map arrow)⟩

/-- Proposition 4.4(iv): every source arrow maps to an isometry. -/
theorem localization_map_isIsometric
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsometric
      ((localizationFunctor (Phi := Phi) (data := data)).map arrow) :=
  isIsometric _

/-- Proposition 4.4(iv): localization preserves and reflects isotropic objects. -/
theorem localization_obj_isIsotropic_iff (object : Carrier Phi data) :
    (preFrobenioid (Phi := Phi) (data := data)).IsIsotropic
        ((localizationFunctor (Phi := Phi) (data := data)).obj object) ↔
      (Carrier.preFrobenioid Phi data).IsIsotropic object :=
  ⟨fun _ ↦ Carrier.isIsotropic Phi data object,
    fun _ ↦ isIsotropic
      ((localizationFunctor (Phi := Phi) (data := data)).obj object)⟩

end Carrier.ColimitBirationalObject

end

end Iut.SourceModelFrobenioid
