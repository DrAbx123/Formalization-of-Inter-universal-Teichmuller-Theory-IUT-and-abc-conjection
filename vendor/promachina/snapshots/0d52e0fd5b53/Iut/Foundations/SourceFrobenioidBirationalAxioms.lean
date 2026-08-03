/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidBirationalDictionary
import Iut.Foundations.SourceFrobenioidModelType
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Frobenioid axioms for arbitrary birationalization

This file proves the presentation-independent Frobenioid axioms in the
corrected form of Frobenioids I, Proposition 4.4(ii).  Mochizuki's official
correction (29) retains the group-like pre-Frobenioid and faithful-localization
claims for an arbitrary Frobenioid, but requires the source to be of
birationally Frobenius-normalized type before the birational target is a full
Frobenioid.  The first layer below transports Definition 1.3(i) from an
arbitrary source `FrobenioidPresentation` to its birational localization; the
final package makes precisely that additional hypothesis explicit.

No coordinates from the concrete Theorem 5.2 model occur here.
-/

open CategoryTheory

namespace Iut.FrobenioidBirationalization

universe u

noncomputable section

variable (F : FrobenioidPresentation.{u})

/-- A source Frobenius trivialization maps to a Frobenius trivialization in
the generic birational target. -/
def localizationFrobeniusTrivialization
    (object : F.carrier)
    (trivialization :
      F.preFrobenioid.FrobeniusTrivialization object) :
    (preFrobenioid F).FrobeniusTrivialization
      ((localizationFunctor F).obj object) where
  lift degree := (localizationFunctor F).map
    (trivialization.lift degree)
  map_one := by
    rw [trivialization.map_one, (localizationFunctor F).map_id]
  map_mul first second := by
    rw [trivialization.map_mul, (localizationFunctor F).map_comp]
  degree_section degree := by
    rw [localization_map_frobeniusDegree,
      trivialization.degree_section]
  base_identity degree := by
    change (preFrobenioid F).base.map
      ((localizationFunctor F).map (trivialization.lift degree)) = _
    rw [localization_map_base]
    change F.preFrobenioid.base.map (trivialization.lift degree) =
      𝟙 (F.preFrobenioid.base.obj object)
    exact trivialization.base_identity degree
  of_frobenius_type degree :=
    (localization_map_isOfFrobeniusType_iff F
      (trivialization.lift degree)).2
      ⟨(trivialization.of_frobenius_type degree).1.1,
        (trivialization.of_frobenius_type degree).2⟩

/-- The source normal form used for Definition 1.3(ii) after
birationalization: a co-angular base-isomorphism is a Frobenius-type arrow
followed by a co-angular pre-step. -/
private structure FrobeniusDenominatorFactorization
    {source target : F.carrier} (arrow : source ⟶ target) where
  midpoint : F.carrier
  frobenius : source ⟶ midpoint
  denominator : midpoint ⟶ target
  frobenius_type : F.preFrobenioid.IsOfFrobeniusType frobenius
  denominator_property : denominators F denominator
  composite : frobenius ≫ denominator = arrow

/-- Obtain the Frobenius/denominator normal form from Definition 1.3(iv).
The final pull-back has invertible base and is therefore an isomorphism; the
co-angularity of the original arrow then forces the middle pre-step to be
co-angular as well. -/
private def frobeniusDenominatorFactorization
    {source target : F.carrier} (arrow : source ⟶ target)
    (coAngular : F.preFrobenioid.IsCoAngular arrow)
    (baseIso : F.preFrobenioid.IsBaseIso arrow) :
    FrobeniusDenominatorFactorization F arrow := by
  let factorization := Classical.choice (F.axioms.factorization arrow)
  have pullbackBaseIso :
      F.preFrobenioid.IsBaseIso factorization.pullback := by
    have firstBaseIso : IsIso
        (F.preFrobenioid.base.map
          (factorization.frobenius ≫ factorization.preStep)) := by
      rw [F.preFrobenioid.base.map_comp]
      haveI : IsIso
          (F.preFrobenioid.base.map factorization.frobenius) :=
        factorization.frobenius_type.2
      haveI : IsIso
          (F.preFrobenioid.base.map factorization.preStep) :=
        factorization.preStep_type.2
      infer_instance
    letI : IsIso
        (F.preFrobenioid.base.map
          (factorization.frobenius ≫ factorization.preStep)) :=
      firstBaseIso
    have compositeBaseIso : IsIso
        (F.preFrobenioid.base.map
          ((factorization.frobenius ≫ factorization.preStep) ≫
            factorization.pullback)) := by
      rw [Category.assoc, factorization.composite]
      exact baseIso
    letI : IsIso
        (F.preFrobenioid.base.map
          ((factorization.frobenius ≫ factorization.preStep) ≫
            factorization.pullback)) := compositeBaseIso
    change IsIso (F.preFrobenioid.base.map factorization.pullback)
    exact IsIso.of_isIso_fac_left
      (F.preFrobenioid.base.map_comp
        (factorization.frobenius ≫ factorization.preStep)
        factorization.pullback).symm
  have pullbackIso : IsIso factorization.pullback :=
    isIso_of_pullback_baseIso F factorization.pullback
      factorization.pullback_type pullbackBaseIso
  letI : IsIso factorization.pullback := pullbackIso
  have pullbackProperty : denominators F factorization.pullback :=
    ⟨isPreStep_of_isIso F factorization.pullback,
      isCoAngular_of_isIso F factorization.pullback⟩
  have preStepCoAngular :
      F.preFrobenioid.IsCoAngular factorization.preStep :=
    factorization_preStep_coAngular F factorization coAngular pullbackIso
  let postStep := factorization.preStep ≫ factorization.pullback
  have postStepProperty : denominators F postStep :=
    denominators_comp F factorization.preStep factorization.pullback
      ⟨factorization.preStep_type, preStepCoAngular⟩ pullbackProperty
  exact
    { midpoint := factorization.frobeniusCodomain
      frobenius := factorization.frobenius
      denominator := postStep
      frobenius_type := factorization.frobenius_type
      denominator_property := postStepProperty
      composite := by
        change factorization.frobenius ≫
          (factorization.preStep ≫ factorization.pullback) = arrow
        simpa only [Category.assoc] using factorization.composite }

/-- Definition 1.3(i)(a) for an arbitrary Frobenioid's birational target. -/
theorem birational_baseRepresented (base : F.baseCategory) :
    ∃ object : BirationalCategory F,
      (preFrobenioid F).IsFrobeniusTrivial object ∧
        Nonempty ((preFrobenioid F).base.obj object ≅ base) := by
  obtain ⟨object, ⟨trivialization⟩, baseIso⟩ :=
    F.axioms.baseRepresented base
  refine ⟨(localizationFunctor F).obj object,
    ⟨localizationFrobeniusTrivialization F object trivialization⟩, ?_⟩
  change Nonempty (F.preFrobenioid.base.obj object ≅ base)
  exact baseIso

/-- Definition 1.3(ii) for an arbitrary Frobenioid's birational target.
The source degree witness supplies the chosen arrow.  An arbitrary target
Frobenius roof is reduced to a source Frobenius arrow followed by an inverted
denominator; source essential uniqueness and the corresponding naturality
square then give the unique target comparison isomorphism. -/
def birational_frobeniusDegree
    (object : BirationalCategory F) (degree : ℕ+) :
    (preFrobenioid F).FrobeniusDegreeWitness object degree := by
  rcases object with ⟨⟨sourceObject⟩⟩
  let sourceWitness := F.axioms.frobeniusDegree sourceObject degree
  refine
    { codomain := (localizationFunctor F).obj sourceWitness.codomain
      hom := (localizationFunctor F).map sourceWitness.hom
      ofFrobeniusType :=
        (localization_map_isOfFrobeniusType_iff F sourceWitness.hom).2
          ⟨sourceWitness.ofFrobeniusType.1.1,
            sourceWitness.ofFrobeniusType.2⟩
      degree := (localization_map_frobeniusDegree F
        sourceWitness.hom).trans sourceWitness.degree
      essentiallyUnique := ?_ }
  intro target arrow arrowType arrowDegree
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let fractionDenominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F fractionDenominator fraction.f =
        arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  have numeratorProperties :
      F.preFrobenioid.IsCoAngular fraction.f ∧
        F.preFrobenioid.IsBaseIso fraction.f :=
    (roofValue_isOfFrobeniusType_iff F fractionDenominator
      fraction.f).1 (by rw [roofEquals]; exact arrowType)
  have numeratorDegree :
      F.preFrobenioid.frobeniusDegree fraction.f = degree := by
    have equality := roofValue_frobeniusDegree F fractionDenominator
      fraction.f
    rw [roofEquals] at equality
    exact equality.symm.trans arrowDegree
  let numeratorFactor := frobeniusDenominatorFactorization F fraction.f
    numeratorProperties.1 numeratorProperties.2
  have numeratorFrobeniusDegree :
      F.preFrobenioid.frobeniusDegree numeratorFactor.frobenius =
        degree := by
    have equality := congrArg F.preFrobenioid.frobeniusDegree
      numeratorFactor.composite
    rw [F.preFrobenioid.frobeniusDegree_comp,
      numeratorFactor.denominator_property.1.1,
      numeratorDegree] at equality
    simpa using equality
  let domainWitness := F.axioms.frobeniusDegree fraction.X' degree
  let numeratorComparisonExistence :=
    domainWitness.essentiallyUnique numeratorFactor.frobenius
      numeratorFactor.frobenius_type numeratorFrobeniusDegree
  let numeratorComparison := Classical.choose
    numeratorComparisonExistence
  have numeratorComparisonRelation :
      domainWitness.hom ≫ numeratorComparison.hom =
        numeratorFactor.frobenius :=
    (Classical.choose_spec numeratorComparisonExistence).1
  have naturalityCompositeCoAngular :
      F.preFrobenioid.IsCoAngular
        (fraction.s ≫ sourceWitness.hom) :=
    F.axioms.coAngular_comp fraction.s sourceWitness.hom
      fraction.hs.2 sourceWitness.ofFrobeniusType.1.1
  have naturalityCompositeBaseIso :
      F.preFrobenioid.IsBaseIso
        (fraction.s ≫ sourceWitness.hom) := by
    change IsIso
      (F.preFrobenioid.base.map (fraction.s ≫ sourceWitness.hom))
    rw [F.preFrobenioid.base.map_comp]
    haveI : IsIso (F.preFrobenioid.base.map fraction.s) :=
      fraction.hs.1.2
    haveI : IsIso (F.preFrobenioid.base.map sourceWitness.hom) :=
      sourceWitness.ofFrobeniusType.2
    infer_instance
  let naturalityFactor := frobeniusDenominatorFactorization F
    (fraction.s ≫ sourceWitness.hom) naturalityCompositeCoAngular
      naturalityCompositeBaseIso
  have naturalityCompositeDegree :
      F.preFrobenioid.frobeniusDegree
          (fraction.s ≫ sourceWitness.hom) = degree := by
    rw [F.preFrobenioid.frobeniusDegree_comp,
      fraction.hs.1.1, sourceWitness.degree]
    simp
  have naturalityFrobeniusDegree :
      F.preFrobenioid.frobeniusDegree naturalityFactor.frobenius =
        degree := by
    have equality := congrArg F.preFrobenioid.frobeniusDegree
      naturalityFactor.composite
    rw [F.preFrobenioid.frobeniusDegree_comp,
      naturalityFactor.denominator_property.1.1,
      naturalityCompositeDegree] at equality
    simpa using equality
  let naturalityComparisonExistence :=
    domainWitness.essentiallyUnique naturalityFactor.frobenius
      naturalityFactor.frobenius_type naturalityFrobeniusDegree
  let naturalityComparison := Classical.choose
    naturalityComparisonExistence
  have naturalityComparisonRelation :
      domainWitness.hom ≫ naturalityComparison.hom =
        naturalityFactor.frobenius :=
    (Classical.choose_spec naturalityComparisonExistence).1
  let naturalityDenominator :=
    naturalityComparison.hom ≫ naturalityFactor.denominator
  have naturalityComparisonProperty : denominators F
      naturalityComparison.hom :=
    ⟨isPreStep_of_isIso F naturalityComparison.hom,
      isCoAngular_of_isIso F naturalityComparison.hom⟩
  have naturalityDenominatorProperty : denominators F
      naturalityDenominator :=
    denominators_comp F naturalityComparison.hom
      naturalityFactor.denominator naturalityComparisonProperty
      naturalityFactor.denominator_property
  have naturalityRelation :
      domainWitness.hom ≫ naturalityDenominator =
        fraction.s ≫ sourceWitness.hom := by
    calc
      domainWitness.hom ≫ naturalityDenominator =
          (domainWitness.hom ≫ naturalityComparison.hom) ≫
            naturalityFactor.denominator := by
        simp only [naturalityDenominator, Category.assoc]
      _ = naturalityFactor.frobenius ≫
          naturalityFactor.denominator := by
        rw [naturalityComparisonRelation]
      _ = fraction.s ≫ sourceWitness.hom :=
        naturalityFactor.composite
  let naturalityIso := Localization.isoOfHom
    (localizationFunctor F) (denominators F) naturalityDenominator
      naturalityDenominatorProperty
  let numeratorComparisonIso :=
    (localizationFunctor F).mapIso numeratorComparison
  let numeratorDenominatorIso := Localization.isoOfHom
    (localizationFunctor F) (denominators F)
      numeratorFactor.denominator numeratorFactor.denominator_property
  let comparison := naturalityIso.symm ≪≫ numeratorComparisonIso ≪≫
    numeratorDenominatorIso
  have mappedNaturalityRelation :
      (localizationFunctor F).map domainWitness.hom ≫
          (localizationFunctor F).map naturalityDenominator =
        (localizationFunctor F).map fraction.s ≫
          (localizationFunctor F).map sourceWitness.hom := by
    rw [← (localizationFunctor F).map_comp,
      ← (localizationFunctor F).map_comp, naturalityRelation]
  have comparisonRelation :
      (localizationFunctor F).map sourceWitness.hom ≫
          comparison.hom = arrow := by
    have mappedFractionDenominatorIso :
        IsIso ((localizationFunctor F).map fraction.s) :=
      MorphismProperty.Q_inverts (denominators F) fraction.s fraction.hs
    letI : IsIso ((localizationFunctor F).map fraction.s) :=
      mappedFractionDenominatorIso
    apply (cancel_epi ((localizationFunctor F).map fraction.s)).1
    calc
      (localizationFunctor F).map fraction.s ≫
          ((localizationFunctor F).map sourceWitness.hom ≫
            comparison.hom) =
          ((localizationFunctor F).map domainWitness.hom ≫
              (localizationFunctor F).map naturalityDenominator) ≫
            comparison.hom := by
        rw [mappedNaturalityRelation]
        simp only [Category.assoc]
      _ = (localizationFunctor F).map domainWitness.hom ≫
          (localizationFunctor F).map numeratorComparison.hom ≫
          (localizationFunctor F).map numeratorFactor.denominator := by
        simp [comparison, naturalityIso, numeratorComparisonIso,
          numeratorDenominatorIso, Category.assoc]
      _ = (localizationFunctor F).map numeratorFactor.frobenius ≫
          (localizationFunctor F).map numeratorFactor.denominator := by
        rw [← (localizationFunctor F).map_comp,
          ← (localizationFunctor F).map_comp]
        simpa only [Category.assoc,
          (localizationFunctor F).map_comp] using congrArg
          (fun value ↦
            (localizationFunctor F).map
              (value ≫ numeratorFactor.denominator))
          numeratorComparisonRelation
      _ = (localizationFunctor F).map fraction.f := by
        rw [← (localizationFunctor F).map_comp,
          numeratorFactor.composite]
      _ = (localizationFunctor F).map fraction.s ≫ arrow := by
        rw [← roofEquals]
        exact (localization_map_denominator_comp_roofValue F
          fractionDenominator fraction.f).symm
  refine ⟨comparison, comparisonRelation, ?_⟩
  intro candidate candidateRelation
  apply Iso.ext
  have mappedWitnessEpi : Epi
      ((localizationFunctor F).map sourceWitness.hom) :=
    localization_map_epi F sourceWitness.hom
  letI : Epi ((localizationFunctor F).map sourceWitness.hom) :=
    mappedWitnessEpi
  apply (cancel_epi ((localizationFunctor F).map sourceWitness.hom)).1
  exact candidateRelation.trans comparisonRelation.symm

/-- A source common-pre-step witness maps to the generic birational target. -/
def localizationCommonPreStepWitness
    (left right : F.carrier)
    (baseIso : F.preFrobenioid.base.obj left ≅
      F.preFrobenioid.base.obj right)
    (witness : F.preFrobenioid.CommonPreStepWitness left right baseIso) :
    (preFrobenioid F).CommonPreStepWitness
      ((localizationFunctor F).obj left)
      ((localizationFunctor F).obj right) baseIso where
  midpoint := (localizationFunctor F).obj witness.midpoint
  toLeft := (localizationFunctor F).map witness.toLeft
  toRight := (localizationFunctor F).map witness.toRight
  toLeft_preStep :=
    (localization_map_isPreStep_iff F witness.toLeft).2
      witness.toLeft_preStep
  toRight_preStep :=
    (localization_map_isPreStep_iff F witness.toRight).2
      witness.toRight_preStep
  leftBaseInverse := witness.leftBaseInverse
  leftBaseInverse_hom := by
    rw [localization_map_base]
    exact witness.leftBaseInverse_hom
  hom_leftBaseInverse := by
    rw [localization_map_base]
    exact witness.hom_leftBaseInverse
  comparison := by
    rw [localization_map_base]
    exact witness.comparison

/-- Definition 1.3(i)(b) for arbitrary objects of the generic birational
target. -/
def birational_commonPreSteps
    (left right : BirationalCategory F)
    (baseIso : (preFrobenioid F).base.obj left ≅
      (preFrobenioid F).base.obj right) :
    (preFrobenioid F).CommonPreStepWitness left right baseIso := by
  rcases left with ⟨⟨leftSource⟩⟩
  rcases right with ⟨⟨rightSource⟩⟩
  let witness := Classical.choice
    (F.axioms.commonPreSteps leftSource rightSource baseIso)
  exact localizationCommonPreStepWitness F leftSource rightSource
    baseIso witness

/-- A source pullback-slice object maps to a pullback-slice object in the
generic birational target. -/
def localizationPullbackSliceObject
    {object : F.carrier}
    (value : PreFrobenioid.PullbackSliceObject object) :
    PreFrobenioid.PullbackSliceObject
      ((localizationFunctor F).obj object) where
  source := (localizationFunctor F).obj value.source
  hom := (localizationFunctor F).map value.hom

/-- The base-slice projection of a mapped pullback slice is definitionally
the source projection after applying the base-arrow dictionary. -/
def localizationBaseSliceIso
    {object : F.carrier}
    (value : PreFrobenioid.PullbackSliceObject object)
    (target : (preFrobenioid F).BaseSliceObject
      ((localizationFunctor F).obj object))
    (sourceIso : F.preFrobenioid.BaseSliceIso
      (value.toBase F.preFrobenioid)
      { source := target.source
        hom := target.hom }) :
    (preFrobenioid F).BaseSliceIso
      ((localizationPullbackSliceObject F value).toBase
        (preFrobenioid F)) target where
  iso := sourceIso.iso
  hom_commutes := by
    change sourceIso.iso.hom ≫ target.hom =
      (preFrobenioid F).base.map
        ((localizationFunctor F).map value.hom)
    rw [localization_map_base]
    exact sourceIso.hom_commutes

/-- Two base-slice morphisms agree when their underlying base arrows agree. -/
theorem birational_baseSliceHom_ext
    {object : BirationalCategory F}
    {left right : (preFrobenioid F).BaseSliceObject object}
    {first second : (preFrobenioid F).BaseSliceHom left right}
    (homEquality : first.hom = second.hom) : first = second := by
  cases first
  cases second
  cases homEquality
  rfl

/-- A base-slice arrow has a unique lift between two target pullback slices.
This is a formal consequence of the pullback universal property itself. -/
def birationalPullbackSlicePreimage
    (object : BirationalCategory F)
    (left right : PreFrobenioid.PullbackSliceObject object)
    (_leftPullback : (preFrobenioid F).IsPullback left.hom)
    (rightPullback : (preFrobenioid F).IsPullback right.hom)
    (value : (preFrobenioid F).BaseSliceHom
      (left.toBase (preFrobenioid F))
      (right.toBase (preFrobenioid F))) :
    PreFrobenioid.PullbackSliceHom left right := by
  let comparison : (preFrobenioid F).PullbackComparisonTarget
      right.hom left.source :=
    { toCodomain := left.hom
      toBaseDomain := value.hom
      commutes := value.commutes.symm }
  let lift := Classical.choose
    ((rightPullback left.source).2 comparison)
  have liftComparison := Classical.choose_spec
    ((rightPullback left.source).2 comparison)
  exact
    { hom := lift
      commutes := congrArg
        PreFrobenioid.PullbackComparisonTarget.toCodomain
        liftComparison }

/-- The lifted pullback-slice arrow projects to the prescribed base arrow. -/
theorem birationalPullbackSlicePreimage_toBase
    (object : BirationalCategory F)
    (left right : PreFrobenioid.PullbackSliceObject object)
    (leftPullback : (preFrobenioid F).IsPullback left.hom)
    (rightPullback : (preFrobenioid F).IsPullback right.hom)
    (value : (preFrobenioid F).BaseSliceHom
      (left.toBase (preFrobenioid F))
      (right.toBase (preFrobenioid F))) :
    (birationalPullbackSlicePreimage F object left right leftPullback
      rightPullback value).toBase (preFrobenioid F) = value := by
  have homEquality := congrArg
    PreFrobenioid.PullbackComparisonTarget.toBaseDomain
    (Classical.choose_spec ((rightPullback left.source).2
      { toCodomain := left.hom
        toBaseDomain := value.hom
        commutes := value.commutes.symm }))
  apply birational_baseSliceHom_ext F
  exact homEquality

/-- Projection from target pullback slices to base slices is fully faithful.
The proof is coordinate-free and uses only the right-hand pullback universal
property. -/
theorem birational_pullbackSliceProjection_bijective
    (object : BirationalCategory F)
    (left right : PreFrobenioid.PullbackSliceObject object)
    (leftPullback : (preFrobenioid F).IsPullback left.hom)
    (rightPullback : (preFrobenioid F).IsPullback right.hom) :
    Function.Bijective
      (fun value : PreFrobenioid.PullbackSliceHom left right ↦
        value.toBase (preFrobenioid F)) := by
  constructor
  · intro first second baseEquality
    cases first with
    | mk first firstCommutes =>
      cases second with
      | mk second secondCommutes =>
        congr 1
        apply (rightPullback left.source).1
        apply pullbackComparisonTarget_ext F
        · exact firstCommutes.trans secondCommutes.symm
        · exact congrArg PreFrobenioid.BaseSliceHom.hom baseEquality
  · intro value
    refine ⟨birationalPullbackSlicePreimage F object left right
      leftPullback rightPullback value, ?_⟩
    exact birationalPullbackSlicePreimage_toBase F object left right
      leftPullback rightPullback value

/-- Definition 1.3(i)(c) for an arbitrary Frobenioid's birational target. -/
def birational_pullbackBaseSlices
    (object : BirationalCategory F) :
    (preFrobenioid F).PullbackBaseSliceEquivalence object := by
  rcases object with ⟨⟨sourceObject⟩⟩
  exact
    { essentiallySurjective := by
        intro target
        let sourceTarget : F.preFrobenioid.BaseSliceObject sourceObject :=
          { source := target.source
            hom := target.hom }
        obtain ⟨sourceValue, sourcePullback, ⟨sourceIso⟩⟩ :=
          (F.axioms.pullbackBaseSlices sourceObject).essentiallySurjective
            sourceTarget
        have sourceProperties :=
          F.axioms.pullback_linear_lbInvertible sourceValue.hom
            sourcePullback
        refine ⟨localizationPullbackSliceObject F sourceValue,
          (localization_map_isPullback_iff F sourceValue.hom).2 ?_,
          ⟨localizationBaseSliceIso F sourceValue target sourceIso⟩⟩
        exact ⟨sourceProperties.2.1, sourceProperties.1⟩
      fullyFaithful := by
        intro left right leftPullback rightPullback
        exact birational_pullbackSliceProjection_bijective F _ left right
          leftPullback rightPullback }

/-- Conjugate a linear base-identity endomorphism forward across a target
isomorphism. -/
def birationalUnitTransportForward
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (arrowIsIso : IsIso arrow)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism source) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism target := by
  letI : IsIso arrow := arrowIsIso
  refine
    { hom := inv arrow ≫ value.hom ≫ arrow
      linear := ?_
      baseIdentity := ?_ }
  · have inverseLinear :=
      (birational_isPreStep_of_isIso F (inv arrow) inferInstance).1
    have arrowLinear :=
      (birational_isPreStep_of_isIso F arrow inferInstance).1
    rw [PreFrobenioid.IsLinear,
      (preFrobenioid F).frobeniusDegree_comp,
      (preFrobenioid F).frobeniusDegree_comp,
      inverseLinear, value.linear, arrowLinear]
    rfl
  · rw [PreFrobenioid.IsBaseIdentity,
      (preFrobenioid F).base.map_comp,
      (preFrobenioid F).base.map_comp,
      value.baseIdentity]
    simp

/-- Conjugate a linear base-identity endomorphism backward across a target
isomorphism. -/
def birationalUnitTransportBackward
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (arrowIsIso : IsIso arrow)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism target) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism source := by
  letI : IsIso arrow := arrowIsIso
  refine
    { hom := arrow ≫ value.hom ≫ inv arrow
      linear := ?_
      baseIdentity := ?_ }
  · have arrowLinear :=
      (birational_isPreStep_of_isIso F arrow inferInstance).1
    have inverseLinear :=
      (birational_isPreStep_of_isIso F (inv arrow) inferInstance).1
    rw [PreFrobenioid.IsLinear,
      (preFrobenioid F).frobeniusDegree_comp,
      (preFrobenioid F).frobeniusDegree_comp,
      arrowLinear, value.linear, inverseLinear]
    rfl
  · rw [PreFrobenioid.IsBaseIdentity,
      (preFrobenioid F).base.map_comp,
      (preFrobenioid F).base.map_comp,
      value.baseIdentity]
    simp

/-- Conjugation across a target isomorphism is a multiplicative
equivalence of linear base-identity endomorphism monoids. -/
def birationalUnitTransportEquiv
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (arrowIsIso : IsIso arrow) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism source ≃*
      (preFrobenioid F).LinearBaseIdentityEndomorphism target := by
  letI : IsIso arrow := arrowIsIso
  refine
    { toFun := birationalUnitTransportForward F arrow arrowIsIso
      invFun := birationalUnitTransportBackward F arrow arrowIsIso
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro value
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    dsimp [birationalUnitTransportForward,
      birationalUnitTransportBackward]
    simp
  · intro value
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    dsimp [birationalUnitTransportForward,
      birationalUnitTransportBackward]
    simp
  · intro left right
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    dsimp [birationalUnitTransportForward]
    change inv arrow ≫ (left.hom ≫ right.hom) ≫ arrow =
      (inv arrow ≫ left.hom ≫ arrow) ≫
        (inv arrow ≫ right.hom ≫ arrow)
    simp

/-- An arbitrary target arrow is invertible exactly when it is a co-angular
pre-step.  The reverse implication is checked on an arbitrary right-fraction
representative. -/
theorem birational_isIso_iff_isPreStep_and_isCoAngular
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    IsIso arrow ↔
      (preFrobenioid F).IsPreStep arrow ∧
        (preFrobenioid F).IsCoAngular arrow := by
  constructor
  · intro arrowIsIso
    letI : IsIso arrow := arrowIsIso
    have targetIdentityCoAngular :
        (preFrobenioid F).IsCoAngular (𝟙 target) := by
      rcases target with ⟨⟨targetSource⟩⟩
      have mappedIdentityCoAngular :
          (preFrobenioid F).IsCoAngular
            ((localizationFunctor F).map (𝟙 targetSource)) :=
        (localization_map_isCoAngular_iff F (𝟙 targetSource)).2
          (isCoAngular_id F targetSource)
      rw [(localizationFunctor F).map_id] at mappedIdentityCoAngular
      change (preFrobenioid F).IsCoAngular
        (𝟙 ((localizationFunctor F).obj targetSource))
      exact mappedIdentityCoAngular
    have arrowCoAngular :
        (preFrobenioid F).IsCoAngular (arrow ≫ 𝟙 target) :=
      (birational_isCoAngular_comp_iso_left_iff F arrow (𝟙 target)).2
        targetIdentityCoAngular
    rw [Category.comp_id] at arrowCoAngular
    exact ⟨birational_isPreStep_of_isIso F arrow arrowIsIso,
      arrowCoAngular⟩
  · rintro ⟨arrowPreStep, arrowCoAngular⟩
    rcases source with ⟨⟨sourceObject⟩⟩
    rcases target with ⟨⟨targetObject⟩⟩
    letI := hasRightCalculusOfFractions F
    obtain ⟨fraction, represents⟩ :=
      Localization.exists_rightFraction
        (L := localizationFunctor F) (W := denominators F) arrow
    let denominator : CoAngularPreStepOver F sourceObject :=
      { source := fraction.X'
        hom := fraction.s
        property := fraction.hs }
    have roofEquals :
        CoAngularPreStepOver.roofValue F denominator fraction.f =
          arrow := by
      change fraction.map (localizationFunctor F)
        (MorphismProperty.Q_inverts (denominators F)) = arrow
      exact represents.symm
    rw [← roofEquals]
    exact (roofValue_isIso_iff F denominator fraction.f).2
      ⟨(roofValue_isPreStep_iff F denominator fraction.f).1
          (by rw [roofEquals]; exact arrowPreStep),
        (roofValue_isCoAngular_iff F denominator fraction.f).1
        (by rw [roofEquals]; exact arrowCoAngular)⟩

/-- Definition 1.3(iii)(a) for the generic birational target.  Compose two
right-fraction roofs after refining the first numerator against the second
denominator by Proposition 1.11(vii); the resulting source numerator is
co-angular by the source composition axiom. -/
theorem birational_coAngular_comp
    {source middle target : BirationalCategory F}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstCoAngular : (preFrobenioid F).IsCoAngular first)
    (secondCoAngular : (preFrobenioid F).IsCoAngular second) :
    (preFrobenioid F).IsCoAngular (first ≫ second) := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases middle with ⟨⟨middleObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨firstFraction, firstRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) first
  obtain ⟨secondFraction, secondRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) second
  let firstDenominator : CoAngularPreStepOver F sourceObject :=
    { source := firstFraction.X'
      hom := firstFraction.s
      property := firstFraction.hs }
  let secondDenominator : CoAngularPreStepOver F middleObject :=
    { source := secondFraction.X'
      hom := secondFraction.s
      property := secondFraction.hs }
  have firstRoof :
      CoAngularPreStepOver.roofValue F firstDenominator firstFraction.f =
        first := by
    change firstFraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = first
    exact firstRepresents.symm
  have secondRoof :
      CoAngularPreStepOver.roofValue F secondDenominator
          secondFraction.f = second := by
    change secondFraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = second
    exact secondRepresents.symm
  have firstNumeratorCoAngular :
      F.preFrobenioid.IsCoAngular firstFraction.f :=
    (roofValue_isCoAngular_iff F firstDenominator firstFraction.f).1
      (by rw [firstRoof]; exact firstCoAngular)
  have secondNumeratorCoAngular :
      F.preFrobenioid.IsCoAngular secondFraction.f :=
    (roofValue_isCoAngular_iff F secondDenominator secondFraction.f).1
      (by rw [secondRoof]; exact secondCoAngular)
  obtain ⟨commonSource, refinement, refinementProperty, across,
      square⟩ :=
    hasCoAngularPreStepSquares F secondFraction.s secondFraction.hs
      firstFraction.f
  have refinedFirstCoAngular :
      F.preFrobenioid.IsCoAngular (refinement ≫ firstFraction.f) :=
    F.axioms.coAngular_comp refinement firstFraction.f
      refinementProperty.2 firstNumeratorCoAngular
  have acrossCoAngular : F.preFrobenioid.IsCoAngular across := by
    apply isCoAngular_left_of_comp_preStep F across secondFraction.s
    · rw [← square]
      exact refinedFirstCoAngular
    · exact secondFraction.hs.1
  let compositeDenominator : CoAngularPreStepOver F sourceObject :=
    { source := commonSource
      hom := refinement ≫ firstFraction.s
      property := denominators_comp F refinement firstFraction.s
        refinementProperty firstFraction.hs }
  have compositeDenominatorIsIso : IsIso
      ((localizationFunctor F).map compositeDenominator.hom) :=
    MorphismProperty.Q_inverts (denominators F)
      compositeDenominator.hom compositeDenominator.property
  letI : IsIso
      ((localizationFunctor F).map compositeDenominator.hom) :=
    compositeDenominatorIsIso
  have firstCancellation :
      (localizationFunctor F).map firstFraction.s ≫ first =
        (localizationFunctor F).map firstFraction.f := by
    rw [← firstRoof]
    simpa only [firstDenominator] using
      localization_map_denominator_comp_roofValue F firstDenominator
        firstFraction.f
  have secondCancellation :
      (localizationFunctor F).map secondFraction.s ≫ second =
        (localizationFunctor F).map secondFraction.f := by
    rw [← secondRoof]
    simpa only [secondDenominator] using
      localization_map_denominator_comp_roofValue F secondDenominator
        secondFraction.f
  have mappedSquare :
      (localizationFunctor F).map refinement ≫
          (localizationFunctor F).map firstFraction.f =
        (localizationFunctor F).map across ≫
          (localizationFunctor F).map secondFraction.s := by
    simpa only [(localizationFunctor F).map_comp] using
      congrArg (fun arrow ↦ (localizationFunctor F).map arrow) square
  have compositeRoof :
      CoAngularPreStepOver.roofValue F compositeDenominator
          (across ≫ secondFraction.f) = first ≫ second := by
    apply (cancel_epi
      ((localizationFunctor F).map compositeDenominator.hom)).1
    rw [localization_map_denominator_comp_roofValue]
    symm
    calc
      (localizationFunctor F).map compositeDenominator.hom ≫
            (first ≫ second) =
          ((localizationFunctor F).map refinement ≫
            (localizationFunctor F).map firstFraction.s) ≫
              (first ≫ second) := by
        dsimp [compositeDenominator]
        rw [(localizationFunctor F).map_comp]
      _ = (localizationFunctor F).map refinement ≫
            (((localizationFunctor F).map firstFraction.s ≫ first) ≫
              second) := by
        simp only [Category.assoc]
      _ = (localizationFunctor F).map refinement ≫
            ((localizationFunctor F).map firstFraction.f ≫ second) := by
        exact congrArg
          (fun arrow ↦ (localizationFunctor F).map refinement ≫
            (arrow ≫ second)) firstCancellation
      _ = ((localizationFunctor F).map refinement ≫
              (localizationFunctor F).map firstFraction.f) ≫
            second := (Category.assoc _ _ _).symm
      _ = ((localizationFunctor F).map across ≫
              (localizationFunctor F).map secondFraction.s) ≫
            second := by
        rw [mappedSquare]
      _ = (localizationFunctor F).map across ≫
            ((localizationFunctor F).map secondFraction.s ≫ second) :=
        Category.assoc _ _ _
      _ = (localizationFunctor F).map across ≫
            (localizationFunctor F).map secondFraction.f := by
        exact congrArg
          (fun arrow ↦ (localizationFunctor F).map across ≫ arrow)
          secondCancellation
      _ = (localizationFunctor F).map
            (across ≫ secondFraction.f) := by
        rw [(localizationFunctor F).map_comp]
  have roofCoAngular :
      (preFrobenioid F).IsCoAngular
        (CoAngularPreStepOver.roofValue F compositeDenominator
          (across ≫ secondFraction.f)) :=
    (roofValue_isCoAngular_iff F compositeDenominator
      (across ≫ secondFraction.f)).2
      (F.axioms.coAngular_comp across secondFraction.f acrossCoAngular
        secondNumeratorCoAngular)
  rw [compositeRoof] at roofCoAngular
  change (preFrobenioid F).IsCoAngular (first ≫ second)
  exact roofCoAngular

/-- Definition 1.3(iii)(b) for the generic birational target.  Refine the
two roof denominators to a common source.  The first refined numerator is a
co-angular pre-step, so the source parallel-arrow axiom makes the second
refined numerator co-angular; invertibility of the refinement's base then
reflects co-angularity to the original second numerator. -/
theorem birational_coAngular_parallelToCoAngularPreStep
    {source target : BirationalCategory F} (first second : source ⟶ target)
    (firstPreStep : (preFrobenioid F).IsPreStep first)
    (firstCoAngular : (preFrobenioid F).IsCoAngular first) :
    (preFrobenioid F).IsCoAngular second := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨firstFraction, firstRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) first
  obtain ⟨secondFraction, secondRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) second
  let firstDenominator : CoAngularPreStepOver F sourceObject :=
    { source := firstFraction.X'
      hom := firstFraction.s
      property := firstFraction.hs }
  let secondDenominator : CoAngularPreStepOver F sourceObject :=
    { source := secondFraction.X'
      hom := secondFraction.s
      property := secondFraction.hs }
  have firstRoof :
      CoAngularPreStepOver.roofValue F firstDenominator firstFraction.f =
        first := by
    change firstFraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = first
    exact firstRepresents.symm
  have secondRoof :
      CoAngularPreStepOver.roofValue F secondDenominator
          secondFraction.f = second := by
    change secondFraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = second
    exact secondRepresents.symm
  have firstNumeratorPreStep :
      F.preFrobenioid.IsPreStep firstFraction.f :=
    (roofValue_isPreStep_iff F firstDenominator firstFraction.f).1
      (by rw [firstRoof]; exact firstPreStep)
  have firstNumeratorCoAngular :
      F.preFrobenioid.IsCoAngular firstFraction.f :=
    (roofValue_isCoAngular_iff F firstDenominator firstFraction.f).1
      (by rw [firstRoof]; exact firstCoAngular)
  let square := rightOreSquare_coAngularPreStep F firstFraction.s
    secondFraction.s firstFraction.hs secondFraction.hs
  have acrossCompositeProperty :
      denominators F (square.across ≫ firstFraction.s) := by
    rw [← square.commutes]
    exact denominators_comp F square.refinement secondFraction.s
      square.refinement_property secondFraction.hs
  have acrossProperty : denominators F square.across :=
    denominators_left_of_comp F square.across firstFraction.s
      acrossCompositeProperty firstFraction.hs
  have refinedFirstProperty :
      denominators F (square.across ≫ firstFraction.f) :=
    denominators_comp F square.across firstFraction.f acrossProperty
      ⟨firstNumeratorPreStep, firstNumeratorCoAngular⟩
  have refinedSecondCoAngular :
      F.preFrobenioid.IsCoAngular
        (square.refinement ≫ secondFraction.f) :=
    F.axioms.coAngular_parallelToCoAngularPreStep
      (square.across ≫ firstFraction.f)
      (square.refinement ≫ secondFraction.f)
      refinedFirstProperty.1 refinedFirstProperty.2
  have secondNumeratorCoAngular :
      F.preFrobenioid.IsCoAngular secondFraction.f :=
    isCoAngular_right_of_comp_baseIso F square.refinement
      secondFraction.f square.refinement_property.1.2
      refinedSecondCoAngular
  have roofCoAngular :
      (preFrobenioid F).IsCoAngular
        (CoAngularPreStepOver.roofValue F secondDenominator
          secondFraction.f) :=
    (roofValue_isCoAngular_iff F secondDenominator secondFraction.f).2
      secondNumeratorCoAngular
  rw [secondRoof] at roofCoAngular
  change (preFrobenioid F).IsCoAngular second
  exact roofCoAngular

/-- Definition 1.3(iii)(c)'s unit transport in the generic target is
ordinary conjugation across the co-angular pre-step, which is invertible. -/
def birational_unitTransport
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (preStep : (preFrobenioid F).IsPreStep arrow)
    (coAngular : (preFrobenioid F).IsCoAngular arrow) :
    (preFrobenioid F).CoAngularUnitTransport arrow := by
  have arrowIsIso : IsIso arrow :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F arrow).2
      ⟨preStep, coAngular⟩
  letI : IsIso arrow := arrowIsIso
  exact
    { transport := birationalUnitTransportEquiv F arrow arrowIsIso
      conjugates := by
        intro value
        dsimp [birationalUnitTransportEquiv,
          birationalUnitTransportForward]
        simp }

/-- A target co-angular unit transport is determined by its multiplicative
equivalence. -/
theorem birational_coAngularUnitTransport_ext
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    {left right : (preFrobenioid F).CoAngularUnitTransport arrow}
    (transportEquality : left.transport = right.transport) :
    left = right := by
  cases left
  cases right
  cases transportEquality
  rfl

/-- The conjugation equation uniquely determines target unit transport. -/
theorem birational_unitTransport_unique
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (preStep : (preFrobenioid F).IsPreStep arrow)
    (coAngular : (preFrobenioid F).IsCoAngular arrow)
    (left right : (preFrobenioid F).CoAngularUnitTransport arrow) :
    left = right := by
  have arrowIsIso : IsIso arrow :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F arrow).2
      ⟨preStep, coAngular⟩
  letI : IsIso arrow := arrowIsIso
  apply birational_coAngularUnitTransport_ext F
  apply MulEquiv.ext
  intro value
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply (cancel_epi arrow).1
  exact (left.conjugates value).symm.trans (right.conjugates value)

/-- Every target linear base-identity endomorphism is invertible.  It is a
pre-step by definition and is co-angular because it is parallel to the
identity co-angular pre-step. -/
theorem birational_linearBaseIdentityEndomorphism_isIso
    {object : BirationalCategory F}
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism object) :
    IsIso value.hom := by
  have valuePreStep : (preFrobenioid F).IsPreStep value.hom := by
    refine ⟨value.linear, ?_⟩
    change IsIso ((preFrobenioid F).base.map value.hom)
    rw [value.baseIdentity]
    infer_instance
  have identityPreStep :
      (preFrobenioid F).IsPreStep (𝟙 object) :=
    birational_isPreStep_of_isIso F (𝟙 object) (by infer_instance)
  have identityCoAngular :
      (preFrobenioid F).IsCoAngular (𝟙 object) := by
    exact ((birational_isIso_iff_isPreStep_and_isCoAngular F
      (𝟙 object)).1 (by infer_instance)).2
  have valueCoAngular :
      (preFrobenioid F).IsCoAngular value.hom :=
    birational_coAngular_parallelToCoAngularPreStep F
      (𝟙 object) value.hom identityPreStep identityCoAngular
  exact (birational_isIso_iff_isPreStep_and_isCoAngular F value.hom).2
    ⟨valuePreStep, valueCoAngular⟩

/-- Rational functions in the generic birational target form a group.  The
inverse is the categorical inverse; its base and degree coordinates follow
from functoriality of the target pre-Frobenioid structure. -/
noncomputable instance birationalLinearBaseIdentityEndomorphismGroup
    (object : BirationalCategory F) :
    Group ((preFrobenioid F).LinearBaseIdentityEndomorphism object) where
  inv value := by
    letI : IsIso value.hom :=
      birational_linearBaseIdentityEndomorphism_isIso F value
    exact
      { hom := inv value.hom
        linear := by
          change (preFrobenioid F).frobeniusDegree (inv value.hom) = 1
          have inverseRelation : inv value.hom ≫ value.hom = 𝟙 object := by
            simp
          have degrees := congrArg (preFrobenioid F).frobeniusDegree
            inverseRelation
          rw [(preFrobenioid F).frobeniusDegree_comp,
            value.linear, (preFrobenioid F).frobeniusDegree_id] at degrees
          simpa using degrees
        baseIdentity := by
          change (preFrobenioid F).base.map (inv value.hom) = 𝟙 _
          apply (cancel_mono ((preFrobenioid F).base.map value.hom)).1
          calc
            (preFrobenioid F).base.map (inv value.hom) ≫
                  (preFrobenioid F).base.map value.hom =
                (preFrobenioid F).base.map
                  (inv value.hom ≫ value.hom) :=
              ((preFrobenioid F).base.map_comp _ _).symm
            _ = (preFrobenioid F).base.map (𝟙 object) := by simp
            _ = 𝟙 _ := (preFrobenioid F).base.map_id object
            _ = (preFrobenioid F).base.map value.hom :=
              value.baseIdentity.symm
            _ = 𝟙 _ ≫ (preFrobenioid F).base.map value.hom :=
              (Category.id_comp _).symm }
  inv_mul_cancel value := by
    letI : IsIso value.hom :=
      birational_linearBaseIdentityEndomorphism_isIso F value
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    change inv value.hom ≫ value.hom = 𝟙 object
    simp

/-- Extend a rational endomorphism across a target isotropic hull.  This is
the direct universal-property construction used in Proposition 2.2(iv); it
does not assume that the birational target is already a Frobenioid. -/
def birationalHullEndomorphism
    {object : BirationalCategory F}
    (hull : (preFrobenioid F).IsotropicHull object)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism object) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism hull.hull := by
  let extension := Classical.choose
    (hull.lift (value.hom ≫ hull.hom) hull.isotropic)
  have extensionRelation : hull.hom ≫ extension =
      value.hom ≫ hull.hom :=
    (Classical.choose_spec
      (hull.lift (value.hom ≫ hull.hom) hull.isotropic)).1
  exact
    { hom := extension
      linear := by
        change (preFrobenioid F).frobeniusDegree extension = 1
        have degrees := congrArg (preFrobenioid F).frobeniusDegree
          extensionRelation
        rw [(preFrobenioid F).frobeniusDegree_comp,
          (preFrobenioid F).frobeniusDegree_comp,
          hull.preStep.1, value.linear] at degrees
        simpa using degrees
      baseIdentity := by
        change (preFrobenioid F).base.map extension = 𝟙 _
        have baseEquation := congrArg (preFrobenioid F).base.map
          extensionRelation
        rw [(preFrobenioid F).base.map_comp,
          (preFrobenioid F).base.map_comp, value.baseIdentity]
          at baseEquation
        haveI : Epi ((preFrobenioid F).base.map hull.hom) :=
          F.baseTotallyEpimorphic ((preFrobenioid F).base.map hull.hom)
        apply (cancel_epi ((preFrobenioid F).base.map hull.hom)).1
        simpa using baseEquation }

/-- The hull extension satisfies its defining pull-through equation. -/
theorem birationalHullEndomorphism_relation
    {object : BirationalCategory F}
    (hull : (preFrobenioid F).IsotropicHull object)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism object) :
    hull.hom ≫ (birationalHullEndomorphism F hull value).hom =
      value.hom ≫ hull.hom := by
  exact (Classical.choose_spec
    (hull.lift (value.hom ≫ hull.hom) hull.isotropic)).1

/-- A target rational function has identity base coordinate after applying
the groupified divisor functor. -/
theorem groupifiedBirationalFunctor_map_rationalFunction_base
    (object : F.carrier)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj object)) :
    ((groupifiedBirationalFunctor F).map value.hom).base = 𝟙 _ := by
  letI : IsIso value.hom :=
    birational_linearBaseIdentityEndomorphism_isIso F value
  obtain ⟨roof⟩ := baseIdentityRoof_of_isBaseIdentity F value.hom
    value.baseIdentity
  have localizedRelation :
      (localizationFunctor F).map roof.denominator.hom ≫ value.hom =
        (localizationFunctor F).map roof.numerator := by
    have represented := congrArg
      (fun arrow ↦
        (localizationFunctor F).map roof.denominator.hom ≫ arrow)
      roof.represents
    exact represented.symm.trans
      (localization_map_denominator_comp_roofValue F
        roof.denominator roof.numerator)
  have groupifiedRelation :
      (groupifiedBirationalFunctor F).map
            ((localizationFunctor F).map roof.denominator.hom) ≫
          (groupifiedBirationalFunctor F).map value.hom =
        (groupifiedBirationalFunctor F).map
          ((localizationFunctor F).map roof.numerator) := by
    simpa only [(groupifiedBirationalFunctor F).map_comp] using
      congrArg (fun arrow ↦ (groupifiedBirationalFunctor F).map arrow)
        localizedRelation
  have baseRelation := congrArg GroupifiedElementaryHom.base
    groupifiedRelation
  change
    ((groupifiedBirationalFunctor F).map
          ((localizationFunctor F).map roof.denominator.hom)).base ≫
        ((groupifiedBirationalFunctor F).map value.hom).base =
      ((groupifiedBirationalFunctor F).map
        ((localizationFunctor F).map roof.numerator)).base at baseRelation
  rw [groupifiedBirationalFunctor_map_localizationFunctor_base,
    groupifiedBirationalFunctor_map_localizationFunctor_base] at baseRelation
  haveI : IsIso (F.preFrobenioid.base.map roof.denominator.hom) :=
    roof.denominator.property.1.2
  apply (cancel_epi (F.preFrobenioid.base.map roof.denominator.hom)).1
  rw [roof.baseEquivalent] at baseRelation
  exact baseRelation.trans (Category.comp_id _).symm

/-- A target rational function has Frobenius degree one after applying the
groupified divisor functor. -/
theorem groupifiedBirationalFunctor_map_rationalFunction_frobeniusDegree
    (object : F.carrier)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj object)) :
    ((groupifiedBirationalFunctor F).map value.hom).frobeniusDegree = 1 := by
  letI : IsIso value.hom :=
    birational_linearBaseIdentityEndomorphism_isIso F value
  obtain ⟨roof⟩ := baseIdentityRoof_of_isBaseIdentity F value.hom
    value.baseIdentity
  have numeratorProperty : denominators F roof.numerator :=
    (roofValue_isIso_iff F roof.denominator roof.numerator).1 (by
      rw [roof.represents]
      infer_instance)
  have localizedRelation :
      (localizationFunctor F).map roof.denominator.hom ≫ value.hom =
        (localizationFunctor F).map roof.numerator := by
    have represented := congrArg
      (fun arrow ↦
        (localizationFunctor F).map roof.denominator.hom ≫ arrow)
      roof.represents
    exact represented.symm.trans
      (localization_map_denominator_comp_roofValue F
        roof.denominator roof.numerator)
  have groupifiedRelation :
      (groupifiedBirationalFunctor F).map
            ((localizationFunctor F).map roof.denominator.hom) ≫
          (groupifiedBirationalFunctor F).map value.hom =
        (groupifiedBirationalFunctor F).map
          ((localizationFunctor F).map roof.numerator) := by
    simpa only [(groupifiedBirationalFunctor F).map_comp] using
      congrArg (fun arrow ↦ (groupifiedBirationalFunctor F).map arrow)
        localizedRelation
  have degreeRelation := congrArg GroupifiedElementaryHom.frobeniusDegree
    groupifiedRelation
  change
    ((groupifiedBirationalFunctor F).map
          ((localizationFunctor F).map roof.denominator.hom)).frobeniusDegree *
        ((groupifiedBirationalFunctor F).map value.hom).frobeniusDegree =
      ((groupifiedBirationalFunctor F).map
        ((localizationFunctor F).map roof.numerator)).frobeniusDegree
      at degreeRelation
  rw [groupifiedBirationalFunctor_map_localizationFunctor_frobeniusDegree,
    groupifiedBirationalFunctor_map_localizationFunctor_frobeniusDegree,
    roof.denominator.property.1.1, numeratorProperty.1.1] at degreeRelation
  simpa using degreeRelation

/-- The `Phi^gp` divisor coordinate of a target rational function is
multiplicative (additive after forgetting `Multiplicative`).  This is the
objectwise map whose image will define `Phi^birat`. -/
def birationalRationalFunctionDivisorHom
    (object : F.carrier) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism
        ((localizationFunctor F).obj object) →*
      Multiplicative
        (Algebra.GrothendieckAddGroup
          (F.preFrobenioid.divisorMonoid.obj
            (F.preFrobenioid.base.obj object)).carrier) where
  toFun value := Multiplicative.ofAdd
    ((groupifiedBirationalFunctor F).map value.hom).divisor
  map_one' := by
    apply Multiplicative.ext
    change ((groupifiedBirationalFunctor F).map (𝟙 _)).divisor = 0
    rw [(groupifiedBirationalFunctor F).map_id]
    rfl
  map_mul' left right := by
    have leftImageBase :=
      groupifiedBirationalFunctor_map_rationalFunction_base F object left
    have rightImageDegree :=
      groupifiedBirationalFunctor_map_rationalFunction_frobeniusDegree
        F object right
    apply Multiplicative.ext
    change ((groupifiedBirationalFunctor F).map
          (left.hom ≫ right.hom)).divisor =
      ((groupifiedBirationalFunctor F).map left.hom).divisor +
        ((groupifiedBirationalFunctor F).map right.hom).divisor
    rw [(groupifiedBirationalFunctor F).map_comp]
    change
      F.preFrobenioid.divisorMonoid.gpPullback
          ((groupifiedBirationalFunctor F).map left.hom).base
          ((groupifiedBirationalFunctor F).map right.hom).divisor +
        ((groupifiedBirationalFunctor F).map right.hom).frobeniusDegree.1 •
          ((groupifiedBirationalFunctor F).map left.hom).divisor = _
    rw [leftImageBase, rightImageDegree,
      F.preFrobenioid.divisorMonoid.gpPullback_id]
    change
      ((groupifiedBirationalFunctor F).map right.hom).divisor +
          (1 : ℕ) •
            ((groupifiedBirationalFunctor F).map left.hom).divisor =
        ((groupifiedBirationalFunctor F).map left.hom).divisor +
          ((groupifiedBirationalFunctor F).map right.hom).divisor
    rw [one_nsmul, add_comm]

/-- The objectwise image of target rational-function divisors inside
`Phi^gp`.  Proposition 4.4(iii)'s `Phi^birat` is obtained by proving that
these images depend only on the base object and are stable under pullback. -/
def birationalDivisorRange
    (object : F.carrier) :
    AddSubgroup
      (Algebra.GrothendieckAddGroup
        (F.preFrobenioid.divisorMonoid.obj
          (F.preFrobenioid.base.obj object)).carrier) :=
  Subgroup.toAddSubgroup'
    (birationalRationalFunctionDivisorHom F object).range

/-- Membership in the objectwise birational divisor range is literal
representability by a target rational function. -/
theorem mem_birationalDivisorRange_iff
    (object : F.carrier)
    (divisor : Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj
        (F.preFrobenioid.base.obj object)).carrier) :
    divisor ∈ birationalDivisorRange F object ↔
      ∃ value : (preFrobenioid F).LinearBaseIdentityEndomorphism
          ((localizationFunctor F).obj object),
        ((groupifiedBirationalFunctor F).map value.hom).divisor =
          divisor := by
  change Multiplicative.ofAdd divisor ∈
      (birationalRationalFunctionDivisorHom F object).range ↔ _
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨value, equality⟩
    exact ⟨value, congrArg Multiplicative.toAdd equality⟩
  · rintro ⟨value, equality⟩
    exact ⟨value, congrArg Multiplicative.ofAdd equality⟩

/-- The rational-function divisor map is surjective onto its canonical
objectwise image. -/
theorem birationalRationalFunctionDivisorHom_surjective
    (object : F.carrier) :
    ∀ divisor : birationalDivisorRange F object,
      ∃ value : (preFrobenioid F).LinearBaseIdentityEndomorphism
          ((localizationFunctor F).obj object),
        ((groupifiedBirationalFunctor F).map value.hom).divisor =
          divisor.1 := by
  intro divisor
  exact (mem_birationalDivisorRange_iff F object divisor.1).1
    divisor.property

/-- A source linear base-identity endomorphism maps to a target rational
function. -/
def localizationLinearBaseIdentityEndomorphism
    (object : F.carrier)
    (sourceValue : F.preFrobenioid.LinearBaseIdentityEndomorphism object) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj object) :=
    { hom := (localizationFunctor F).map sourceValue.hom
      linear := (localization_map_isLinear_iff F sourceValue.hom).2
        sourceValue.linear
      baseIdentity := by
        change (preFrobenioid F).base.map
            ((localizationFunctor F).map sourceValue.hom) = 𝟙 _
        rw [localization_map_base]
        exact sourceValue.baseIdentity }

/-- A source base-identity automorphism maps to a target rational-function
endomorphism. -/
def localizationUnitEndomorphism
    (object : F.carrier)
    (unit : F.preFrobenioid.BaseIdentityAutomorphism object) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj object) := by
  letI : IsIso unit.iso.hom := unit.iso.isIso_hom
  exact localizationLinearBaseIdentityEndomorphism F object
    { hom := unit.iso.hom
      linear := (isPreStep_of_isIso F unit.iso.hom).1
      baseIdentity := unit.baseIdentity }

/-- The image of every source rational endomorphism is central among all target
rational functions.  A target rational function is a fraction of two source
co-angular pre-steps with the same base arrow.  Pulling the source value back
along the denominator or numerator gives the same value, by Definition
1.3(iii)(c), and the two conjugation equations give the claim after cancelling
the denominator. -/
theorem localizationLinearBaseIdentityEndomorphism_central
    (object : F.carrier)
    (sourceValue : F.preFrobenioid.LinearBaseIdentityEndomorphism object)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj object)) :
    (localizationLinearBaseIdentityEndomorphism F object sourceValue).hom ≫
        value.hom =
      value.hom ≫
        (localizationLinearBaseIdentityEndomorphism F object sourceValue).hom := by
  letI : IsIso value.hom :=
    birational_linearBaseIdentityEndomorphism_isIso F value
  obtain ⟨roof⟩ := baseIdentityRoof_of_isBaseIdentity F value.hom
    value.baseIdentity
  have numeratorProperty : denominators F roof.numerator :=
    (roofValue_isIso_iff F roof.denominator roof.numerator).1 (by
      rw [roof.represents]
      infer_instance)
  let denominatorTransport := F.axioms.unitTransport
    roof.denominator.hom roof.denominator.property.1
      roof.denominator.property.2
  let numeratorTransport := F.axioms.unitTransport roof.numerator
    numeratorProperty.1 numeratorProperty.2
  have transportEquality : numeratorTransport.transport =
      denominatorTransport.transport :=
    F.axioms.unitTransport_dependsOnlyOnBase roof.numerator
      roof.denominator.hom numeratorProperty.1 numeratorProperty.2
      roof.denominator.property.1 roof.denominator.property.2
      roof.baseEquivalent
  let pulledUnit := denominatorTransport.transport.symm sourceValue
  have denominatorImage :
      denominatorTransport.transport pulledUnit = sourceValue :=
    denominatorTransport.transport.apply_symm_apply sourceValue
  have numeratorImage :
      numeratorTransport.transport pulledUnit = sourceValue := by
    exact (DFunLike.congr_fun transportEquality pulledUnit).trans
      denominatorImage
  have denominatorRelation :
      pulledUnit.hom ≫ roof.denominator.hom =
        roof.denominator.hom ≫ sourceValue.hom := by
    simpa only [denominatorImage] using
      denominatorTransport.conjugates pulledUnit
  have numeratorRelation :
      pulledUnit.hom ≫ roof.numerator =
        roof.numerator ≫ sourceValue.hom := by
    simpa only [numeratorImage] using
      numeratorTransport.conjugates pulledUnit
  have mappedDenominatorRelation := congrArg
    (fun arrow ↦ (localizationFunctor F).map arrow)
    denominatorRelation
  have mappedNumeratorRelation := congrArg
    (fun arrow ↦ (localizationFunctor F).map arrow)
    numeratorRelation
  change (localizationFunctor F).map
      (pulledUnit.hom ≫ roof.denominator.hom) =
    (localizationFunctor F).map
      (roof.denominator.hom ≫ sourceValue.hom) at mappedDenominatorRelation
  change (localizationFunctor F).map
      (pulledUnit.hom ≫ roof.numerator) =
    (localizationFunctor F).map
      (roof.numerator ≫ sourceValue.hom) at mappedNumeratorRelation
  simp only [(localizationFunctor F).map_comp] at mappedDenominatorRelation mappedNumeratorRelation
  rw [← roof.represents]
  have mappedDenominatorIso :
      IsIso ((localizationFunctor F).map roof.denominator.hom) :=
    MorphismProperty.Q_inverts (denominators F) roof.denominator.hom
      roof.denominator.property
  letI : IsIso ((localizationFunctor F).map roof.denominator.hom) :=
    mappedDenominatorIso
  apply (cancel_epi
    ((localizationFunctor F).map roof.denominator.hom)).1
  calc
    (localizationFunctor F).map roof.denominator.hom ≫
          ((localizationLinearBaseIdentityEndomorphism F object
              sourceValue).hom ≫
            CoAngularPreStepOver.roofValue F roof.denominator
              roof.numerator) =
        ((localizationFunctor F).map roof.denominator.hom ≫
          (localizationFunctor F).map sourceValue.hom) ≫
            CoAngularPreStepOver.roofValue F roof.denominator
              roof.numerator := by
      simp only [localizationLinearBaseIdentityEndomorphism,
        Category.assoc]
    _ = ((localizationFunctor F).map pulledUnit.hom ≫
          (localizationFunctor F).map roof.denominator.hom) ≫
            CoAngularPreStepOver.roofValue F roof.denominator
              roof.numerator := by
      rw [mappedDenominatorRelation]
    _ = (localizationFunctor F).map pulledUnit.hom ≫
          (localizationFunctor F).map roof.numerator := by
      rw [Category.assoc,
        localization_map_denominator_comp_roofValue]
    _ = (localizationFunctor F).map roof.numerator ≫
          (localizationFunctor F).map sourceValue.hom :=
      mappedNumeratorRelation
    _ = ((localizationFunctor F).map roof.denominator.hom ≫
          CoAngularPreStepOver.roofValue F roof.denominator
            roof.numerator) ≫
          (localizationLinearBaseIdentityEndomorphism F object
            sourceValue).hom := by
      simp only [localizationLinearBaseIdentityEndomorphism,
        localization_map_denominator_comp_roofValue]
    _ = (localizationFunctor F).map roof.denominator.hom ≫
        (CoAngularPreStepOver.roofValue F roof.denominator
          roof.numerator ≫
            (localizationLinearBaseIdentityEndomorphism F object
              sourceValue).hom) := by
      simp only [Category.assoc]

/-- Proposition 4.4(iii), kernel clause: a target rational function has zero
groupified divisor exactly when it is the image of a source unit. -/
theorem birational_groupifiedDivisor_eq_zero_iff_sourceUnitImage
    (object : F.carrier)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj object)) :
    ((groupifiedBirationalFunctor F).map value.hom).divisor = 0 ↔
      ∃ unit : F.preFrobenioid.BaseIdentityAutomorphism object,
        localizationUnitEndomorphism F object unit = value := by
  constructor
  · intro divisorZero
    letI : IsIso value.hom :=
      birational_linearBaseIdentityEndomorphism_isIso F value
    obtain ⟨roof⟩ := baseIdentityRoof_of_isBaseIdentity F value.hom
      value.baseIdentity
    have numeratorProperty : denominators F roof.numerator :=
      (roofValue_isIso_iff F roof.denominator roof.numerator).1 (by
        rw [roof.represents]
        infer_instance)
    let denominatorImage := (groupifiedBirationalFunctor F).map
      ((localizationFunctor F).map roof.denominator.hom)
    let numeratorImage := (groupifiedBirationalFunctor F).map
      ((localizationFunctor F).map roof.numerator)
    let valueImage := (groupifiedBirationalFunctor F).map value.hom
    have localizedRelation :
        (localizationFunctor F).map roof.denominator.hom ≫ value.hom =
          (localizationFunctor F).map roof.numerator := by
      have represented := congrArg
        (fun arrow ↦
          (localizationFunctor F).map roof.denominator.hom ≫ arrow)
        roof.represents
      exact represented.symm.trans
        (localization_map_denominator_comp_roofValue F
          roof.denominator roof.numerator)
    have groupifiedRelation : denominatorImage ≫ valueImage =
        numeratorImage := by
      simpa only [denominatorImage, numeratorImage, valueImage,
        (groupifiedBirationalFunctor F).map_comp] using
        congrArg (fun arrow ↦ (groupifiedBirationalFunctor F).map arrow)
          localizedRelation
    have valueDegree : valueImage.frobeniusDegree = 1 := by
      have degrees := congrArg GroupifiedElementaryHom.frobeniusDegree
        groupifiedRelation
      change denominatorImage.frobeniusDegree *
          valueImage.frobeniusDegree =
        numeratorImage.frobeniusDegree at degrees
      rw [show denominatorImage.frobeniusDegree = 1 by
          exact (groupifiedBirationalFunctor_map_localizationFunctor_frobeniusDegree
            F roof.denominator.hom).trans roof.denominator.property.1.1,
        show numeratorImage.frobeniusDegree = 1 by
          exact (groupifiedBirationalFunctor_map_localizationFunctor_frobeniusDegree
            F roof.numerator).trans numeratorProperty.1.1] at degrees
      simpa using degrees
    have imageDivisorEquality : denominatorImage.divisor =
        numeratorImage.divisor := by
      have valueDegreeValue : valueImage.frobeniusDegree.1 = 1 :=
        congrArg (fun degree : ℕ+ ↦ degree.1) valueDegree
      have divisors := congrArg GroupifiedElementaryHom.divisor
        groupifiedRelation
      change F.preFrobenioid.divisorMonoid.gpPullback
            denominatorImage.base valueImage.divisor +
          valueImage.frobeniusDegree.1 • denominatorImage.divisor =
        numeratorImage.divisor at divisors
      rw [show valueImage.divisor = 0 by exact divisorZero,
        map_zero, zero_add, valueDegreeValue, one_nsmul] at divisors
      exact divisors
    have sourceGroupifiedDivisorEquality :
        Algebra.GrothendieckAddGroup.of
            (F.preFrobenioid.divisor roof.denominator.hom) =
          Algebra.GrothendieckAddGroup.of
            (F.preFrobenioid.divisor roof.numerator) := by
      simpa only [denominatorImage, numeratorImage,
        groupifiedBirationalFunctor_map_localizationFunctor_divisor] using
        imageDivisorEquality
    let divisorMonoid := F.preFrobenioid.divisorMonoid.obj
      (F.preFrobenioid.base.obj roof.denominator.source)
    letI : IsLeftCancelAdd divisorMonoid.carrier :=
      ⟨fun first second third equality ↦
        divisorMonoid.integral first second third equality⟩
    letI : IsCancelAdd divisorMonoid.carrier :=
      AddCommMagma.IsLeftCancelAdd.toIsCancelAdd divisorMonoid.carrier
    have sourceDivisorEquality :
        F.preFrobenioid.divisor roof.numerator =
          F.preFrobenioid.divisor roof.denominator.hom := by
      exact Algebra.GrothendieckAddGroup.of_injective
        sourceGroupifiedDivisorEquality.symm
    obtain ⟨unit, unitEquation, _unitUnique⟩ :=
      F.axioms.faithfulUpToUnits roof.numerator
        roof.denominator.hom roof.baseEquivalent sourceDivisorEquality
        numeratorProperty.1 numeratorProperty.2
        roof.denominator.property.1 roof.denominator.property.2
    refine ⟨unit, ?_⟩
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    have mappedDenominatorIso :
        IsIso ((localizationFunctor F).map roof.denominator.hom) :=
      MorphismProperty.Q_inverts (denominators F)
        roof.denominator.hom roof.denominator.property
    letI : IsIso ((localizationFunctor F).map roof.denominator.hom) :=
      mappedDenominatorIso
    apply (cancel_epi
      ((localizationFunctor F).map roof.denominator.hom)).1
    have mappedUnitEquation := congrArg
      (fun arrow ↦ (localizationFunctor F).map arrow) unitEquation
    change (localizationFunctor F).map
        (roof.denominator.hom ≫ unit.iso.hom) =
      (localizationFunctor F).map roof.numerator at mappedUnitEquation
    simp only [(localizationFunctor F).map_comp] at mappedUnitEquation
    calc
      (localizationFunctor F).map roof.denominator.hom ≫
          (localizationUnitEndomorphism F object unit).hom =
        (localizationFunctor F).map roof.numerator := by
          simpa only [localizationUnitEndomorphism,
            localizationLinearBaseIdentityEndomorphism] using
            mappedUnitEquation
      _ = (localizationFunctor F).map roof.denominator.hom ≫ value.hom :=
        localizedRelation.symm
  · rintro ⟨unit, rfl⟩
    letI : IsIso unit.iso.hom := unit.iso.isIso_hom
    have unitIsometric : F.preFrobenioid.IsIsometric unit.iso.hom :=
      isIsometric_of_isIso F unit.iso.hom
    change ((groupifiedBirationalFunctor F).map
      ((localizationFunctor F).map unit.iso.hom)).divisor = 0
    rw [groupifiedBirationalFunctor_map_localizationFunctor_divisor,
      unitIsometric]
    exact map_zero _

/-- Proposition 4.4(iii)'s exact kernel clause, expressed for the packaged
rational-function divisor homomorphism. -/
theorem birationalRationalFunctionDivisorHom_eq_one_iff_sourceUnitImage
    (object : F.carrier)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj object)) :
    birationalRationalFunctionDivisorHom F object value = 1 ↔
      ∃ unit : F.preFrobenioid.BaseIdentityAutomorphism object,
        localizationUnitEndomorphism F object unit = value := by
  change Multiplicative.ofAdd
      ((groupifiedBirationalFunctor F).map value.hom).divisor = 1 ↔ _
  rw [ofAdd_eq_one]
  exact birational_groupifiedDivisor_eq_zero_iff_sourceUnitImage
    F object value

/-- Base-identity automorphisms in the generic target are determined by
their underlying isomorphisms. -/
theorem birational_baseIdentityAutomorphism_ext
    {object : BirationalCategory F}
    {left right : (preFrobenioid F).BaseIdentityAutomorphism object}
    (isoEquality : left.iso = right.iso) : left = right := by
  cases left
  cases right
  cases isoEquality
  rfl

/-- Definition 1.3(vi) in the generic target.  Two parallel co-angular
pre-steps are isomorphisms, so their unique correcting unit is their
categorical quotient. -/
theorem birational_faithfulUpToUnits
    {source target : BirationalCategory F} (first second : source ⟶ target)
    (baseEquality : (preFrobenioid F).base.map first =
      (preFrobenioid F).base.map second)
    (_divisorEquality : (preFrobenioid F).divisor first =
      (preFrobenioid F).divisor second)
    (firstPreStep : (preFrobenioid F).IsPreStep first)
    (firstCoAngular : (preFrobenioid F).IsCoAngular first)
    (secondPreStep : (preFrobenioid F).IsPreStep second)
    (secondCoAngular : (preFrobenioid F).IsCoAngular second) :
    ∃! alpha : (preFrobenioid F).BaseIdentityAutomorphism target,
      second ≫ alpha.iso.hom = first := by
  have firstIsIso : IsIso first :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F first).2
      ⟨firstPreStep, firstCoAngular⟩
  have secondIsIso : IsIso second :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F second).2
      ⟨secondPreStep, secondCoAngular⟩
  letI : IsIso first := firstIsIso
  letI : IsIso second := secondIsIso
  let correctingIso := (asIso second).symm ≪≫ asIso first
  let correcting :
      (preFrobenioid F).BaseIdentityAutomorphism target :=
    { iso := correctingIso
      baseIdentity := by
        change (preFrobenioid F).base.map
          (inv second ≫ first) = 𝟙 _
        rw [(preFrobenioid F).base.map_comp,
          Functor.map_inv, baseEquality]
        simp }
  refine ⟨correcting, by simp [correcting, correctingIso], ?_⟩
  intro candidate candidateEquation
  apply birational_baseIdentityAutomorphism_ext F
  apply Iso.ext
  apply (cancel_epi second).1
  simpa [correcting, correctingIso] using candidateEquation

/-- The unique outgoing representative of the terminal target divisor. -/
def birational_outgoingDivisorRepresentative
    (object : BirationalCategory F)
    (divisor : (preFrobenioid F).DivisorOrder object) :
    (preFrobenioid F).OutgoingCoAngularPreStep object divisor where
  target := object
  hom := 𝟙 object
  preStep := (birational_isIso_iff_isPreStep_and_isCoAngular F
    (𝟙 object)).1 inferInstance |>.1
  coAngular := (birational_isIso_iff_isPreStep_and_isCoAngular F
    (𝟙 object)).1 inferInstance |>.2
  divisor_eq := by cases divisor; rfl

/-- The outgoing divisor-order slice over the terminal target monoid is fully
faithful. -/
theorem birational_outgoingDivisorOrderFullyFaithful
    {object : BirationalCategory F}
    {leftDivisor rightDivisor : (preFrobenioid F).DivisorOrder object}
    (left : (preFrobenioid F).OutgoingCoAngularPreStep
      object leftDivisor)
    (right : (preFrobenioid F).OutgoingCoAngularPreStep
      object rightDivisor) :
    leftDivisor ≤ rightDivisor ↔
      ∃! arrow : left.target ⟶ right.target,
        left.hom ≫ arrow = right.hom := by
  haveI : IsIso left.hom :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F left.hom).2
      ⟨left.preStep, left.coAngular⟩
  constructor
  · intro _
    refine ⟨inv left.hom ≫ right.hom, by simp, ?_⟩
    intro arrow equality
    apply (cancel_epi left.hom).1
    simpa using equality
  · intro _
    exact ⟨0, by cases leftDivisor; cases rightDivisor; rfl⟩

/-- Outgoing representatives of the terminal target divisor are uniquely
isomorphic. -/
theorem birational_outgoingDivisorRepresentative_unique
    {object : BirationalCategory F}
    {divisor : (preFrobenioid F).DivisorOrder object}
    (left right : (preFrobenioid F).OutgoingCoAngularPreStep
      object divisor) :
    ∃! iso : left.target ≅ right.target,
      left.hom ≫ iso.hom = right.hom := by
  haveI : IsIso left.hom :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F left.hom).2
      ⟨left.preStep, left.coAngular⟩
  haveI : IsIso right.hom :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F right.hom).2
      ⟨right.preStep, right.coAngular⟩
  let iso := (asIso left.hom).symm ≪≫ asIso right.hom
  refine ⟨iso, by simp [iso], ?_⟩
  intro candidate equality
  apply Iso.ext
  apply (cancel_epi left.hom).1
  simpa [iso] using equality

/-- Every incoming co-angular pre-step determines the sole target divisor. -/
theorem birational_incomingDivisor
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    ∃! divisor : (preFrobenioid F).DivisorOrder target,
      (preFrobenioid F).divisorMonoid.pullback
          ((preFrobenioid F).base.map arrow) divisor =
        (preFrobenioid F).divisor arrow := by
  refine ⟨PUnit.unit, rfl, ?_⟩
  intro value _
  cases value
  rfl

/-- The unique incoming representative of the terminal target divisor. -/
def birational_incomingDivisorRepresentative
    (object : BirationalCategory F)
    (divisor : (preFrobenioid F).DivisorOrder object) :
    (preFrobenioid F).IncomingCoAngularPreStep object divisor where
  source := object
  hom := 𝟙 object
  preStep := (birational_isIso_iff_isPreStep_and_isCoAngular F
    (𝟙 object)).1 inferInstance |>.1
  coAngular := (birational_isIso_iff_isPreStep_and_isCoAngular F
    (𝟙 object)).1 inferInstance |>.2
  pulledBack_divisor_eq := by cases divisor; rfl

/-- The incoming divisor-order slice over the terminal target monoid is fully
faithful. -/
theorem birational_incomingDivisorOrderFullyFaithful
    {object : BirationalCategory F}
    {leftDivisor rightDivisor : (preFrobenioid F).DivisorOrder object}
    (left : (preFrobenioid F).IncomingCoAngularPreStep
      object leftDivisor)
    (right : (preFrobenioid F).IncomingCoAngularPreStep
      object rightDivisor) :
    rightDivisor ≤ leftDivisor ↔
      ∃! arrow : left.source ⟶ right.source,
        arrow ≫ right.hom = left.hom := by
  haveI : IsIso right.hom :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F right.hom).2
      ⟨right.preStep, right.coAngular⟩
  constructor
  · intro _
    refine ⟨left.hom ≫ inv right.hom, by simp, ?_⟩
    intro arrow equality
    apply (cancel_mono right.hom).1
    simpa using equality
  · intro _
    exact ⟨0, by cases leftDivisor; cases rightDivisor; rfl⟩

/-- Incoming representatives of the terminal target divisor are uniquely
isomorphic. -/
theorem birational_incomingDivisorRepresentative_unique
    {object : BirationalCategory F}
    {divisor : (preFrobenioid F).DivisorOrder object}
    (left right : (preFrobenioid F).IncomingCoAngularPreStep
      object divisor) :
    ∃! iso : left.source ≅ right.source,
      iso.hom ≫ right.hom = left.hom := by
  haveI : IsIso left.hom :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F left.hom).2
      ⟨left.preStep, left.coAngular⟩
  haveI : IsIso right.hom :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F right.hom).2
      ⟨right.preStep, right.coAngular⟩
  let iso := asIso left.hom ≪≫ (asIso right.hom).symm
  refine ⟨iso, by simp [iso], ?_⟩
  intro candidate equality
  apply Iso.ext
  apply (cancel_mono right.hom).1
  simpa [iso] using equality

/-- Proposition 4.4(ii): every arrow in the generic birational target is
epic.  A roof is an inverted denominator followed by the localized source
numerator; both factors are epic. -/
theorem birational_totallyEpimorphic
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    Epi arrow := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F denominator fraction.f = arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  have mappedNumeratorEpi :
      Epi ((localizationFunctor F).map fraction.f) :=
    localization_map_epi F fraction.f
  letI : Epi ((localizationFunctor F).map fraction.f) :=
    mappedNumeratorEpi
  have mappedDenominatorIso :
      IsIso ((localizationFunctor F).map denominator.hom) :=
    MorphismProperty.Q_inverts (denominators F) denominator.hom
      denominator.property
  letI : IsIso ((localizationFunctor F).map denominator.hom) :=
    mappedDenominatorIso
  rw [← roofEquals]
  change Epi
    (inv ((localizationFunctor F).map denominator.hom) ≫
      (localizationFunctor F).map fraction.f)
  infer_instance

/-- Every isomorphism in the generic target satisfies the pull-back
universal property. -/
theorem birational_isPullback_of_isIso
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    [IsIso arrow] : (preFrobenioid F).IsPullback arrow := by
  intro test
  constructor
  · intro left right equality
    apply (cancel_mono arrow).1
    exact congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain equality
  · intro comparison
    refine ⟨comparison.toCodomain ≫ inv arrow, ?_⟩
    apply pullbackComparisonTarget_ext F
    · change (comparison.toCodomain ≫ inv arrow) ≫ arrow =
        comparison.toCodomain
      simp
    · change (preFrobenioid F).base.map
          (comparison.toCodomain ≫ inv arrow) =
        comparison.toBaseDomain
      rw [(preFrobenioid F).base.map_comp, Functor.map_inv]
      apply (cancel_mono ((preFrobenioid F).base.map arrow)).1
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact comparison.commutes

/-- Every target pull-back is linear and LB-invertible.  On a right-fraction
representative this is exactly the co-angular/linear classification of its
source numerator, together with the terminal target divisor. -/
theorem birational_pullback_linear_lbInvertible
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (pullback : (preFrobenioid F).IsPullback arrow) :
    (preFrobenioid F).IsLinear arrow ∧
      (preFrobenioid F).IsLBInvertible arrow := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F denominator fraction.f =
        arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  have numeratorProperties :
      F.preFrobenioid.IsCoAngular fraction.f ∧
        F.preFrobenioid.IsLinear fraction.f :=
    (roofValue_isPullback_iff F denominator fraction.f).1
      (by rw [roofEquals]; exact pullback)
  constructor
  · rw [← roofEquals]
    exact (roofValue_isLinear_iff F denominator fraction.f).2
      numeratorProperties.2
  · exact ⟨by
      rw [← roofEquals]
      exact (roofValue_isCoAngular_iff F denominator fraction.f).2
        numeratorProperties.1,
      isIsometric F arrow⟩

/-- The groupified target functor and the target pre-Frobenioid have the
same base coordinate on every right-fraction arrow. -/
theorem groupifiedBirationalFunctor_map_base
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    ((groupifiedBirationalFunctor F).map arrow).base =
      (preFrobenioid F).base.map arrow := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ := Localization.exists_rightFraction
    (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F denominator fraction.f = arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  rw [← roofEquals]
  have mappedRelation := congrArg
    (fun candidate ↦ (groupifiedBirationalFunctor F).map candidate)
    (localization_map_denominator_comp_roofValue F denominator fraction.f)
  simp only [(groupifiedBirationalFunctor F).map_comp] at mappedRelation
  have mappedBases := congrArg GroupifiedElementaryHom.base mappedRelation
  change
    ((groupifiedBirationalFunctor F).map
          ((localizationFunctor F).map denominator.hom)).base ≫
        ((groupifiedBirationalFunctor F).map
          (CoAngularPreStepOver.roofValue F denominator fraction.f)).base =
      ((groupifiedBirationalFunctor F).map
        ((localizationFunctor F).map fraction.f)).base at mappedBases
  rw [groupifiedBirationalFunctor_map_localizationFunctor_base,
    groupifiedBirationalFunctor_map_localizationFunctor_base] at mappedBases
  have sourceBases := denominator_base_comp_roofValue_base F
    denominator fraction.f
  haveI : IsIso (F.preFrobenioid.base.map denominator.hom) :=
    denominator.property.1.2
  apply (cancel_epi (F.preFrobenioid.base.map denominator.hom)).1
  exact mappedBases.trans sourceBases.symm

/-- The groupified target functor and the target pre-Frobenioid have the
same Frobenius-degree coordinate on every right-fraction arrow. -/
theorem groupifiedBirationalFunctor_map_frobeniusDegree
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    ((groupifiedBirationalFunctor F).map arrow).frobeniusDegree =
      (preFrobenioid F).frobeniusDegree arrow := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ := Localization.exists_rightFraction
    (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F denominator fraction.f = arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  rw [← roofEquals]
  have mappedRelation := congrArg
    (fun candidate ↦ (groupifiedBirationalFunctor F).map candidate)
    (localization_map_denominator_comp_roofValue F denominator fraction.f)
  simp only [(groupifiedBirationalFunctor F).map_comp] at mappedRelation
  have mappedDegrees := congrArg
    GroupifiedElementaryHom.frobeniusDegree mappedRelation
  change
    ((groupifiedBirationalFunctor F).map
          ((localizationFunctor F).map denominator.hom)).frobeniusDegree *
        ((groupifiedBirationalFunctor F).map
          (CoAngularPreStepOver.roofValue F denominator fraction.f)).frobeniusDegree =
      ((groupifiedBirationalFunctor F).map
        ((localizationFunctor F).map fraction.f)).frobeniusDegree
      at mappedDegrees
  rw [groupifiedBirationalFunctor_map_localizationFunctor_frobeniusDegree,
    groupifiedBirationalFunctor_map_localizationFunctor_frobeniusDegree,
    denominator.property.1.1] at mappedDegrees
  have mappedDegree :
      ((groupifiedBirationalFunctor F).map
        (CoAngularPreStepOver.roofValue F denominator fraction.f)).frobeniusDegree =
          F.preFrobenioid.frobeniusDegree fraction.f := by
    simpa using mappedDegrees
  exact mappedDegree.trans
    (roofValue_frobeniusDegree F denominator fraction.f).symm

/-- The pull-back comparison target used to transport a target rational
function contravariantly through a target pull-back arrow. -/
private def birationalRationalFunctionPullbackTarget
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism target) :
    (preFrobenioid F).PullbackComparisonTarget arrow source where
  toCodomain := arrow ≫ value.hom
  toBaseDomain := 𝟙 _
  commutes := by
    rw [(preFrobenioid F).base.map_comp, value.baseIdentity]
    simp

/-- Contravariant transport of a target rational function through a target
pull-back arrow, constructed directly from the pull-back universal property. -/
def birationalRationalFunctionPullback
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (pullback : (preFrobenioid F).IsPullback arrow)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism target) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism source := by
  let comparison := birationalRationalFunctionPullbackTarget F arrow value
  let lift := Classical.choose ((pullback source).2 comparison)
  have liftComparison := Classical.choose_spec
    ((pullback source).2 comparison)
  refine
    { hom := lift
      linear := ?_
      baseIdentity := ?_ }
  · have relation := congrArg
      PreFrobenioid.PullbackComparisonTarget.toCodomain liftComparison
    change lift ≫ arrow = arrow ≫ value.hom at relation
    have degrees := congrArg (preFrobenioid F).frobeniusDegree relation
    rw [(preFrobenioid F).frobeniusDegree_comp,
      (preFrobenioid F).frobeniusDegree_comp,
      (birational_pullback_linear_lbInvertible F arrow pullback).1,
      value.linear] at degrees
    simpa using degrees
  · exact congrArg
      PreFrobenioid.PullbackComparisonTarget.toBaseDomain liftComparison

/-- The transported rational function is characterized by the usual
pull-through equation. -/
theorem birationalRationalFunctionPullback_relation
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (pullback : (preFrobenioid F).IsPullback arrow)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism target) :
    (birationalRationalFunctionPullback F arrow pullback value).hom ≫ arrow =
      arrow ≫ value.hom := by
  exact congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
    (Classical.choose_spec ((pullback source).2
      (birationalRationalFunctionPullbackTarget F arrow value)))

/-- Divisors of target rational functions are contravariantly natural along
target pull-back arrows. -/
theorem groupifiedBirationalFunctor_map_rationalFunctionPullback_divisor
    {source target : F.carrier}
    (arrow : (localizationFunctor F).obj source ⟶
      (localizationFunctor F).obj target)
    (pullback : (preFrobenioid F).IsPullback arrow)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj target)) :
    ((groupifiedBirationalFunctor F).map
      (birationalRationalFunctionPullback F arrow pullback value).hom).divisor =
      F.preFrobenioid.divisorMonoid.gpPullback
        ((preFrobenioid F).base.map arrow)
        (((groupifiedBirationalFunctor F).map value.hom).divisor) := by
  have mappedRelation := congrArg
    (fun candidate ↦ (groupifiedBirationalFunctor F).map candidate)
    (birationalRationalFunctionPullback_relation F arrow pullback value)
  simp only [(groupifiedBirationalFunctor F).map_comp] at mappedRelation
  have divisors := congrArg GroupifiedElementaryHom.divisor mappedRelation
  change
    F.preFrobenioid.divisorMonoid.gpPullback
          ((groupifiedBirationalFunctor F).map
            (birationalRationalFunctionPullback F arrow pullback value).hom).base
          ((groupifiedBirationalFunctor F).map arrow).divisor +
        ((groupifiedBirationalFunctor F).map arrow).frobeniusDegree.1 •
          ((groupifiedBirationalFunctor F).map
            (birationalRationalFunctionPullback F arrow pullback value).hom).divisor =
      F.preFrobenioid.divisorMonoid.gpPullback
          ((groupifiedBirationalFunctor F).map arrow).base
          ((groupifiedBirationalFunctor F).map value.hom).divisor +
        ((groupifiedBirationalFunctor F).map value.hom).frobeniusDegree.1 •
          ((groupifiedBirationalFunctor F).map arrow).divisor at divisors
  have arrowDegree :
      ((groupifiedBirationalFunctor F).map arrow).frobeniusDegree = 1 := by
    exact (groupifiedBirationalFunctor_map_frobeniusDegree F arrow).trans
      (birational_pullback_linear_lbInvertible F arrow pullback).1
  have arrowBase : ((groupifiedBirationalFunctor F).map arrow).base =
      (preFrobenioid F).base.map arrow :=
    groupifiedBirationalFunctor_map_base F arrow
  rw [groupifiedBirationalFunctor_map_rationalFunction_base,
    groupifiedBirationalFunctor_map_rationalFunction_frobeniusDegree,
    arrowDegree, arrowBase] at divisors
  have positiveOneValue : (1 : ℕ+).1 = (1 : ℕ) := rfl
  simp only [F.preFrobenioid.divisorMonoid.gpPullback_id,
    AddMonoidHom.id_apply, positiveOneValue, one_nsmul] at divisors
  rw [add_comm] at divisors
  exact add_right_cancel divisors

/-- The objectwise rational-divisor image is stable under every target
pull-back arrow between the corresponding source objects. -/
theorem gpPullback_mem_birationalDivisorRange_of_pullback
    {source target : F.carrier}
    (arrow : (localizationFunctor F).obj source ⟶
      (localizationFunctor F).obj target)
    (pullback : (preFrobenioid F).IsPullback arrow)
    {divisor : Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj
        (F.preFrobenioid.base.obj target)).carrier}
    (membership : divisor ∈ birationalDivisorRange F target) :
    F.preFrobenioid.divisorMonoid.gpPullback
        ((preFrobenioid F).base.map arrow) divisor ∈
      birationalDivisorRange F source := by
  obtain ⟨value, valueDivisor⟩ :=
    (mem_birationalDivisorRange_iff F target divisor).1 membership
  apply (mem_birationalDivisorRange_iff F source _).2
  refine ⟨birationalRationalFunctionPullback F arrow pullback value, ?_⟩
  rw [groupifiedBirationalFunctor_map_rationalFunctionPullback_divisor,
    valueDivisor]

/-- Along a target isomorphism, pull-back identifies the two objectwise
rational-divisor images in both directions. -/
theorem gpPullback_mem_birationalDivisorRange_iff_of_isIso
    {source target : F.carrier}
    (arrow : (localizationFunctor F).obj source ⟶
      (localizationFunctor F).obj target)
    [IsIso arrow]
    (divisor : Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj
        (F.preFrobenioid.base.obj target)).carrier) :
    F.preFrobenioid.divisorMonoid.gpPullback
        ((preFrobenioid F).base.map arrow) divisor ∈
          birationalDivisorRange F source ↔
      divisor ∈ birationalDivisorRange F target := by
  constructor
  · intro membership
    have inverseMembership :=
      gpPullback_mem_birationalDivisorRange_of_pullback F (inv arrow)
        (birational_isPullback_of_isIso F (inv arrow)) membership
    have baseComposition := (preFrobenioid F).base.map_comp
      (inv arrow) arrow
    rw [IsIso.inv_hom_id, (preFrobenioid F).base.map_id] at baseComposition
    change
      F.preFrobenioid.divisorMonoid.gpPullback
          ((preFrobenioid F).base.map (inv arrow))
          (F.preFrobenioid.divisorMonoid.gpPullback
            ((preFrobenioid F).base.map arrow) divisor) ∈
        birationalDivisorRange F target at inverseMembership
    rw [← AddMonoidHom.comp_apply,
      ← F.preFrobenioid.divisorMonoid.gpPullback_comp,
      ← baseComposition,
      F.preFrobenioid.divisorMonoid.gpPullback_id,
      AddMonoidHom.id_apply] at inverseMembership
    exact inverseMembership
  · exact gpPullback_mem_birationalDivisorRange_of_pullback F arrow
      (birational_isPullback_of_isIso F arrow)

/-- Definition 1.3(iv)(a)'s factorization for an arbitrary target arrow.
The denominator is absorbed into the Frobenius-type roof, while the source
numerator supplies the pre-step and pull-back stages. -/
theorem birational_factorization
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    Nonempty ((preFrobenioid F).FrobenioidFactorization arrow) := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  let sourceFactorization :=
    Classical.choice (F.axioms.factorization fraction.f)
  have sourcePullbackProperties :=
    F.axioms.pullback_linear_lbInvertible
      sourceFactorization.pullback sourceFactorization.pullback_type
  refine ⟨
    { frobeniusCodomain :=
        (localizationFunctor F).obj sourceFactorization.frobeniusCodomain
      preStepCodomain :=
        (localizationFunctor F).obj sourceFactorization.preStepCodomain
      frobenius := CoAngularPreStepOver.roofValue F denominator
        sourceFactorization.frobenius
      preStep := (localizationFunctor F).map sourceFactorization.preStep
      pullback := (localizationFunctor F).map sourceFactorization.pullback
      frobenius_type :=
        (roofValue_isOfFrobeniusType_iff F denominator
          sourceFactorization.frobenius).2
          ⟨sourceFactorization.frobenius_type.1.1,
            sourceFactorization.frobenius_type.2⟩
      preStep_type :=
        (localization_map_isPreStep_iff F
          sourceFactorization.preStep).2
          sourceFactorization.preStep_type
      pullback_type :=
        (localization_map_isPullback_iff F
          sourceFactorization.pullback).2
          ⟨sourcePullbackProperties.2.1,
            sourcePullbackProperties.1⟩
      composite := ?_ }⟩
  calc
    _ = (CoAngularPreStepOver.roofValue F denominator
          sourceFactorization.frobenius ≫
        (localizationFunctor F).map sourceFactorization.preStep) ≫
          (localizationFunctor F).map sourceFactorization.pullback :=
      (Category.assoc _ _ _).symm
    _ = CoAngularPreStepOver.roofValue F denominator
          (sourceFactorization.frobenius ≫
            sourceFactorization.preStep) ≫
        (localizationFunctor F).map sourceFactorization.pullback := by
      rw [roofValue_comp_localization_map]
    _ = CoAngularPreStepOver.roofValue F denominator
        ((sourceFactorization.frobenius ≫
            sourceFactorization.preStep) ≫
          sourceFactorization.pullback) := by
      rw [roofValue_comp_localization_map]
    _ = CoAngularPreStepOver.roofValue F denominator fraction.f := by
      rw [Category.assoc, sourceFactorization.composite]
    _ = arrow := by
      change fraction.map (localizationFunctor F)
        (MorphismProperty.Q_inverts (denominators F)) = arrow
      exact represents.symm

/-- The Frobenius stage of a target factorization has the degree of the
original arrow.  The pre-step and pull-back stages both have degree one. -/
theorem birational_factorization_frobeniusDegree
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    (factor : (preFrobenioid F).FrobenioidFactorization arrow) :
    (preFrobenioid F).frobeniusDegree factor.frobenius =
      (preFrobenioid F).frobeniusDegree arrow := by
  have preStepLinear := factor.preStep_type.1
  have pullbackLinear :=
    (birational_pullback_linear_lbInvertible F factor.pullback
      factor.pullback_type).1
  have projected := congrArg (preFrobenioid F).frobeniusDegree
    factor.composite
  rw [(preFrobenioid F).frobeniusDegree_comp,
    (preFrobenioid F).frobeniusDegree_comp,
    preStepLinear, pullbackLinear] at projected
  simpa using projected

/-- The comparison between the pull-back stages of two target
factorizations, together with the slice equations used by the middle-stage
comparison. -/
structure BirationalFactorizationPullbackComparison
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    (left right : (preFrobenioid F).FrobenioidFactorization arrow) where
  iso : left.preStepCodomain ≅ right.preStepCodomain
  hom_comp : iso.hom ≫ right.pullback = left.pullback
  inv_comp : iso.inv ≫ left.pullback = right.pullback
  prefix_hom :
    ((preFrobenioid F).base.map left.frobenius ≫
        (preFrobenioid F).base.map left.preStep) ≫
      (preFrobenioid F).base.map iso.hom =
        (preFrobenioid F).base.map right.frobenius ≫
          (preFrobenioid F).base.map right.preStep
  prefix_inv :
    ((preFrobenioid F).base.map right.frobenius ≫
        (preFrobenioid F).base.map right.preStep) ≫
      (preFrobenioid F).base.map iso.inv =
        (preFrobenioid F).base.map left.frobenius ≫
          (preFrobenioid F).base.map left.preStep

/-- The two pull-back universal properties construct inverse comparison
arrows between the pull-back-stage objects. -/
def birational_factorizationPullbackComparison
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    (left right : (preFrobenioid F).FrobenioidFactorization arrow) :
    BirationalFactorizationPullbackComparison F left right := by
  letI : IsIso ((preFrobenioid F).base.map left.frobenius) :=
    left.frobenius_type.2
  letI : IsIso ((preFrobenioid F).base.map left.preStep) :=
    left.preStep_type.2
  letI : IsIso ((preFrobenioid F).base.map right.frobenius) :=
    right.frobenius_type.2
  letI : IsIso ((preFrobenioid F).base.map right.preStep) :=
    right.preStep_type.2
  let leftPrefix := (preFrobenioid F).base.map left.frobenius ≫
    (preFrobenioid F).base.map left.preStep
  let rightPrefix := (preFrobenioid F).base.map right.frobenius ≫
    (preFrobenioid F).base.map right.preStep
  let forwardBase := inv leftPrefix ≫ rightPrefix
  have forwardBaseComp :
      forwardBase ≫ (preFrobenioid F).base.map right.pullback =
        (preFrobenioid F).base.map left.pullback := by
    have leftCompositeBase := congrArg
      (fun value ↦ (preFrobenioid F).base.map value) left.composite
    change (preFrobenioid F).base.map
        (left.frobenius ≫ left.preStep ≫ left.pullback) =
      (preFrobenioid F).base.map arrow at leftCompositeBase
    rw [(preFrobenioid F).base.map_comp,
      (preFrobenioid F).base.map_comp, ← Category.assoc] at leftCompositeBase
    change leftPrefix ≫ (preFrobenioid F).base.map left.pullback =
      (preFrobenioid F).base.map arrow at leftCompositeBase
    have rightCompositeBase := congrArg
      (fun value ↦ (preFrobenioid F).base.map value) right.composite
    change (preFrobenioid F).base.map
        (right.frobenius ≫ right.preStep ≫ right.pullback) =
      (preFrobenioid F).base.map arrow at rightCompositeBase
    rw [(preFrobenioid F).base.map_comp,
      (preFrobenioid F).base.map_comp, ← Category.assoc] at rightCompositeBase
    change rightPrefix ≫ (preFrobenioid F).base.map right.pullback =
      (preFrobenioid F).base.map arrow at rightCompositeBase
    dsimp only [forwardBase]
    rw [Category.assoc, rightCompositeBase, ← leftCompositeBase]
    simp
  let forwardComparison :
      (preFrobenioid F).PullbackComparisonTarget right.pullback
        left.preStepCodomain :=
    { toCodomain := left.pullback
      toBaseDomain := forwardBase
      commutes := forwardBaseComp.symm }
  have forwardExists :=
    (right.pullback_type left.preStepCodomain).2 forwardComparison
  let forward := Classical.choose forwardExists
  have forwardComparisonEq := Classical.choose_spec forwardExists
  have forwardComp : forward ≫ right.pullback = left.pullback :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
      forwardComparisonEq
  have forwardBaseEq :
      (preFrobenioid F).base.map forward = forwardBase :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain
      forwardComparisonEq
  let backwardBase := inv rightPrefix ≫ leftPrefix
  have backwardBaseComp :
      backwardBase ≫ (preFrobenioid F).base.map left.pullback =
        (preFrobenioid F).base.map right.pullback := by
    have leftCompositeBase := congrArg
      (fun value ↦ (preFrobenioid F).base.map value) left.composite
    change (preFrobenioid F).base.map
        (left.frobenius ≫ left.preStep ≫ left.pullback) =
      (preFrobenioid F).base.map arrow at leftCompositeBase
    rw [(preFrobenioid F).base.map_comp,
      (preFrobenioid F).base.map_comp, ← Category.assoc] at leftCompositeBase
    change leftPrefix ≫ (preFrobenioid F).base.map left.pullback =
      (preFrobenioid F).base.map arrow at leftCompositeBase
    have rightCompositeBase := congrArg
      (fun value ↦ (preFrobenioid F).base.map value) right.composite
    change (preFrobenioid F).base.map
        (right.frobenius ≫ right.preStep ≫ right.pullback) =
      (preFrobenioid F).base.map arrow at rightCompositeBase
    rw [(preFrobenioid F).base.map_comp,
      (preFrobenioid F).base.map_comp, ← Category.assoc] at rightCompositeBase
    change rightPrefix ≫ (preFrobenioid F).base.map right.pullback =
      (preFrobenioid F).base.map arrow at rightCompositeBase
    dsimp only [backwardBase]
    rw [Category.assoc, leftCompositeBase, ← rightCompositeBase]
    simp
  let backwardComparison :
      (preFrobenioid F).PullbackComparisonTarget left.pullback
        right.preStepCodomain :=
    { toCodomain := right.pullback
      toBaseDomain := backwardBase
      commutes := backwardBaseComp.symm }
  have backwardExists :=
    (left.pullback_type right.preStepCodomain).2 backwardComparison
  let backward := Classical.choose backwardExists
  have backwardComparisonEq := Classical.choose_spec backwardExists
  have backwardComp : backward ≫ left.pullback = right.pullback :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
      backwardComparisonEq
  have backwardBaseEq :
      (preFrobenioid F).base.map backward = backwardBase :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain
      backwardComparisonEq
  have forwardBackward :
      forward ≫ backward = 𝟙 left.preStepCodomain := by
    apply (left.pullback_type left.preStepCodomain).1
    apply pullbackComparisonTarget_ext F
    · change (forward ≫ backward) ≫ left.pullback =
        𝟙 left.preStepCodomain ≫ left.pullback
      rw [Category.assoc, backwardComp, forwardComp]
      simp
    · change (preFrobenioid F).base.map (forward ≫ backward) =
        𝟙 ((preFrobenioid F).base.obj left.preStepCodomain)
      rw [(preFrobenioid F).base.map_comp, forwardBaseEq,
        backwardBaseEq]
      dsimp only [forwardBase, backwardBase]
      simp
  have backwardForward :
      backward ≫ forward = 𝟙 right.preStepCodomain := by
    apply (right.pullback_type right.preStepCodomain).1
    apply pullbackComparisonTarget_ext F
    · change (backward ≫ forward) ≫ right.pullback =
        𝟙 right.preStepCodomain ≫ right.pullback
      rw [Category.assoc, forwardComp, backwardComp]
      simp
    · change (preFrobenioid F).base.map (backward ≫ forward) =
        𝟙 ((preFrobenioid F).base.obj right.preStepCodomain)
      rw [(preFrobenioid F).base.map_comp, backwardBaseEq,
        forwardBaseEq]
      dsimp only [forwardBase, backwardBase]
      simp
  exact
    { iso :=
        { hom := forward
          inv := backward
          hom_inv_id := forwardBackward
          inv_hom_id := backwardForward }
      hom_comp := forwardComp
      inv_comp := backwardComp
      prefix_hom := by
        rw [forwardBaseEq]
        dsimp only [forwardBase]
        change leftPrefix ≫ inv leftPrefix ≫ rightPrefix = rightPrefix
        exact IsIso.hom_inv_id_assoc leftPrefix rightPrefix
      prefix_inv := by
        rw [backwardBaseEq]
        dsimp only [backwardBase]
        change rightPrefix ≫ inv rightPrefix ≫ leftPrefix = leftPrefix
        exact IsIso.hom_inv_id_assoc rightPrefix leftPrefix }

/-- The equal-degree target Frobenius stages are essentially uniquely
isomorphic. -/
structure BirationalFactorizationFrobeniusComparison
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    (left right : (preFrobenioid F).FrobenioidFactorization arrow) where
  iso : left.frobeniusCodomain ≅ right.frobeniusCodomain
  square : left.frobenius ≫ iso.hom = right.frobenius

/-- Compare the Frobenius stages through the selected target witness of their
common degree. -/
def birational_factorizationFrobeniusComparison
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    (left right : (preFrobenioid F).FrobenioidFactorization arrow) :
    BirationalFactorizationFrobeniusComparison F left right := by
  let witness := birational_frobeniusDegree F source
    ((preFrobenioid F).frobeniusDegree arrow)
  have leftExists := witness.essentiallyUnique left.frobenius
    left.frobenius_type
      (birational_factorization_frobeniusDegree F left)
  let leftIso := Classical.choose leftExists
  have leftSquare : witness.hom ≫ leftIso.hom = left.frobenius :=
    (Classical.choose_spec leftExists).1
  have rightExists := witness.essentiallyUnique right.frobenius
    right.frobenius_type
      (birational_factorization_frobeniusDegree F right)
  let rightIso := Classical.choose rightExists
  have rightSquare : witness.hom ≫ rightIso.hom = right.frobenius :=
    (Classical.choose_spec rightExists).1
  let comparison := leftIso.symm ≪≫ rightIso
  refine ⟨comparison, ?_⟩
  dsimp only [comparison]
  rw [Iso.trans_hom, Iso.symm_hom, ← leftSquare, Category.assoc,
    Iso.hom_inv_id_assoc, rightSquare]

/-- Definition 1.3(iv)(a)'s comparison of arbitrary factorizations in the
generic birational target. -/
def birational_factorizationIso
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    (left right : (preFrobenioid F).FrobenioidFactorization arrow) :
    (preFrobenioid F).FrobenioidFactorizationIso left right := by
  let frobeniusComparison :=
    birational_factorizationFrobeniusComparison F left right
  let pullbackComparison :=
    birational_factorizationPullbackComparison F left right
  let candidate := frobeniusComparison.iso.inv ≫ left.preStep ≫
    pullbackComparison.iso.hom
  have frobeniusInvSquare :
      right.frobenius ≫ frobeniusComparison.iso.inv =
        left.frobenius := by
    rw [← frobeniusComparison.square, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have toCodomainEquality :
      candidate ≫ right.pullback =
        right.preStep ≫ right.pullback := by
    letI : Epi right.frobenius :=
      birational_totallyEpimorphic F right.frobenius
    apply (cancel_epi right.frobenius).1
    dsimp only [candidate]
    have frobeniusWhiskered := congrArg
      (fun value ↦ value ≫ left.preStep ≫
        pullbackComparison.iso.hom ≫ right.pullback)
      frobeniusInvSquare
    calc
      right.frobenius ≫
            (frobeniusComparison.iso.inv ≫ left.preStep ≫
              pullbackComparison.iso.hom) ≫ right.pullback =
          left.frobenius ≫ left.preStep ≫
            pullbackComparison.iso.hom ≫ right.pullback := by
        simpa only [Category.assoc] using frobeniusWhiskered
      _ = left.frobenius ≫ left.preStep ≫ left.pullback := by
        rw [pullbackComparison.hom_comp]
      _ = arrow := left.composite
      _ = right.frobenius ≫ right.preStep ≫ right.pullback :=
        right.composite.symm
  have toBaseEquality :
      (preFrobenioid F).base.map candidate =
        (preFrobenioid F).base.map right.preStep := by
    letI : Epi ((preFrobenioid F).base.map right.frobenius) :=
      F.baseTotallyEpimorphic _
    apply (cancel_epi ((preFrobenioid F).base.map right.frobenius)).1
    have frobeniusInvBase := congrArg
      (fun value ↦ (preFrobenioid F).base.map value)
      frobeniusInvSquare
    change (preFrobenioid F).base.map
        (right.frobenius ≫ frobeniusComparison.iso.inv) =
      (preFrobenioid F).base.map left.frobenius at frobeniusInvBase
    rw [(preFrobenioid F).base.map_comp] at frobeniusInvBase
    dsimp only [candidate]
    rw [(preFrobenioid F).base.map_comp,
      (preFrobenioid F).base.map_comp]
    change (preFrobenioid F).base.map right.frobenius ≫
        ((preFrobenioid F).base.map frobeniusComparison.iso.inv ≫
          (preFrobenioid F).base.map left.preStep ≫
          (preFrobenioid F).base.map pullbackComparison.iso.hom) =
      (preFrobenioid F).base.map right.frobenius ≫
        (preFrobenioid F).base.map right.preStep
    have baseWhiskered := congrArg
      (fun value ↦ value ≫
        (preFrobenioid F).base.map left.preStep ≫
        (preFrobenioid F).base.map pullbackComparison.iso.hom)
      frobeniusInvBase
    calc
      (preFrobenioid F).base.map right.frobenius ≫
          ((preFrobenioid F).base.map frobeniusComparison.iso.inv ≫
            (preFrobenioid F).base.map left.preStep ≫
            (preFrobenioid F).base.map pullbackComparison.iso.hom) =
        (preFrobenioid F).base.map left.frobenius ≫
          (preFrobenioid F).base.map left.preStep ≫
          (preFrobenioid F).base.map pullbackComparison.iso.hom := by
        simpa only [Category.assoc] using baseWhiskered
      _ = (preFrobenioid F).base.map right.frobenius ≫
          (preFrobenioid F).base.map right.preStep := by
        simpa only [Category.assoc] using pullbackComparison.prefix_hom
  have preStepSquare : candidate = right.preStep := by
    apply (right.pullback_type right.frobeniusCodomain).1
    apply pullbackComparisonTarget_ext F
    · exact toCodomainEquality
    · exact toBaseEquality
  exact
    { frobeniusCodomainIso := frobeniusComparison.iso
      preStepCodomainIso := pullbackComparison.iso
      frobenius_square := frobeniusComparison.square
      preStep_square := preStepSquare
      pullback_square := pullbackComparison.inv_comp }

/-- A target factorization comparison is determined by its two object
isomorphisms. -/
theorem birational_frobenioidFactorizationIso_ext
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    {left right : (preFrobenioid F).FrobenioidFactorization arrow}
    {first second :
      (preFrobenioid F).FrobenioidFactorizationIso left right}
    (frobeniusCodomainIso :
      first.frobeniusCodomainIso = second.frobeniusCodomainIso)
    (preStepCodomainIso :
      first.preStepCodomainIso = second.preStepCodomainIso) :
    first = second := by
  cases first
  cases second
  cases frobeniusCodomainIso
  cases preStepCodomainIso
  rfl

/-- Definition 1.3(iv)(a)'s uniqueness clause.  Total epimorphicity first
forces the Frobenius-stage comparison and then the middle-stage comparison. -/
theorem birational_factorizationIso_unique
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    (left right : (preFrobenioid F).FrobenioidFactorization arrow)
    (first second :
      (preFrobenioid F).FrobenioidFactorizationIso left right) :
    first = second := by
  have frobeniusHomEquality :
      first.frobeniusCodomainIso.hom =
        second.frobeniusCodomainIso.hom := by
    letI : Epi left.frobenius :=
      birational_totallyEpimorphic F left.frobenius
    apply (cancel_epi left.frobenius).1
    exact first.frobenius_square.trans second.frobenius_square.symm
  have frobeniusIsoEquality :
      first.frobeniusCodomainIso =
        second.frobeniusCodomainIso := by
    apply Iso.ext
    exact frobeniusHomEquality
  have secondPreStepSquare := second.preStep_square
  rw [← frobeniusIsoEquality] at secondPreStepSquare
  have preStepHomEquality :
      first.preStepCodomainIso.hom =
        second.preStepCodomainIso.hom := by
    let middlePrefix := first.frobeniusCodomainIso.inv ≫ left.preStep
    letI : Epi middlePrefix :=
      birational_totallyEpimorphic F middlePrefix
    apply (cancel_epi middlePrefix).1
    simpa only [middlePrefix, Category.assoc] using
      first.preStep_square.trans secondPreStepSquare.symm
  have preStepIsoEquality :
      first.preStepCodomainIso = second.preStepCodomainIso := by
    apply Iso.ext
    exact preStepHomEquality
  exact birational_frobenioidFactorizationIso_ext F
    frobeniusIsoEquality preStepIsoEquality

/-- A source pre-step factorization of a roof numerator induces a target
pre-step factorization of the roof.  Its first factor absorbs the inverted
denominator; the second factor is the localized source second factor. -/
def localizationPreStepFactorization
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target)
    {coAngularFirst : Bool}
    (factorization : F.preFrobenioid.PreStepFactorization
      numerator coAngularFirst) :
    (preFrobenioid F).PreStepFactorization
      (CoAngularPreStepOver.roofValue F denominator numerator)
      coAngularFirst where
  midpoint := (localizationFunctor F).obj factorization.midpoint
  first := CoAngularPreStepOver.roofValue F denominator
    factorization.first
  second := (localizationFunctor F).map factorization.second
  first_preStep :=
    (roofValue_isPreStep_iff F denominator factorization.first).2
      factorization.first_preStep
  second_preStep :=
    (localization_map_isPreStep_iff F factorization.second).2
      factorization.second_preStep
  first_kind := by
    cases coAngularFirst with
    | false => exact isIsometric F _
    | true =>
        exact (roofValue_isCoAngular_iff F denominator
          factorization.first).2 factorization.first_kind
  second_kind := by
    cases coAngularFirst with
    | false =>
        exact (localization_map_isCoAngular_iff F
          factorization.second).2 factorization.second_kind
    | true => exact isIsometric F _
  composite := by
    rw [roofValue_comp_localization_map, factorization.composite]

/-- Definition 1.3(v)(c), co-angular-then-isometric direction, for the
generic birational target.  Factor the pre-step numerator in the source and
absorb the roof denominator into its first factor. -/
theorem birational_preStep_coAngularThenIsometric
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (arrowPreStep : (preFrobenioid F).IsPreStep arrow) :
    Nonempty ((preFrobenioid F).PreStepFactorization arrow true) := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F denominator fraction.f = arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  have numeratorPreStep : F.preFrobenioid.IsPreStep fraction.f :=
    (roofValue_isPreStep_iff F denominator fraction.f).1
      (by rw [roofEquals]; exact arrowPreStep)
  let sourceFactorization := Classical.choice
    (F.axioms.preStep_coAngularThenIsometric
      fraction.f numeratorPreStep)
  rw [← roofEquals]
  exact ⟨localizationPreStepFactorization F denominator fraction.f
    sourceFactorization⟩

/-- Definition 1.3(v)(c), isometric-then-co-angular direction, for the
generic birational target.  Factor the pre-step numerator in the source and
absorb the roof denominator into its first factor. -/
theorem birational_preStep_isometricThenCoAngular
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (arrowPreStep : (preFrobenioid F).IsPreStep arrow) :
    Nonempty ((preFrobenioid F).PreStepFactorization arrow false) := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F denominator fraction.f = arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  have numeratorPreStep : F.preFrobenioid.IsPreStep fraction.f :=
    (roofValue_isPreStep_iff F denominator fraction.f).1
      (by rw [roofEquals]; exact arrowPreStep)
  let sourceFactorization := Classical.choice
    (F.axioms.preStep_isometricThenCoAngular
      fraction.f numeratorPreStep)
  rw [← roofEquals]
  exact ⟨localizationPreStepFactorization F denominator fraction.f
    sourceFactorization⟩

/-- Definition 1.3(v)(c)'s comparison isomorphism in the generic target.
In either ordering the co-angular pre-step factor is invertible, so it
canonically identifies the two intermediate objects. -/
def birational_preStepFactorizationIso
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    {coAngularFirst : Bool}
    (left right : (preFrobenioid F).PreStepFactorization
      arrow coAngularFirst) :
    (preFrobenioid F).PreStepFactorizationIso left right := by
  cases coAngularFirst with
  | false =>
      have leftCoAngular :
          (preFrobenioid F).IsCoAngular left.second := by
        exact left.second_kind
      have rightCoAngular :
          (preFrobenioid F).IsCoAngular right.second := by
        exact right.second_kind
      letI : IsIso left.second :=
        (birational_isIso_iff_isPreStep_and_isCoAngular F
          left.second).2 ⟨left.second_preStep, leftCoAngular⟩
      letI : IsIso right.second :=
        (birational_isIso_iff_isPreStep_and_isCoAngular F
          right.second).2 ⟨right.second_preStep, rightCoAngular⟩
      let comparison := asIso left.second ≪≫ (asIso right.second).symm
      have secondSquare :
          comparison.inv ≫ left.second = right.second := by
        dsimp only [comparison]
        rw [Iso.trans_inv, Iso.symm_inv]
        simp
      have homSecond :
          comparison.hom ≫ right.second = left.second := by
        rw [← secondSquare, ← Category.assoc, Iso.hom_inv_id,
          Category.id_comp]
      have firstSquare :
          left.first ≫ comparison.hom = right.first := by
        apply (cancel_mono right.second).1
        rw [Category.assoc, homSecond, left.composite, right.composite]
      exact
        { midpointIso := comparison
          first_square := firstSquare
          second_square := secondSquare }
  | true =>
      have leftCoAngular :
          (preFrobenioid F).IsCoAngular left.first := by
        exact left.first_kind
      have rightCoAngular :
          (preFrobenioid F).IsCoAngular right.first := by
        exact right.first_kind
      letI : IsIso left.first :=
        (birational_isIso_iff_isPreStep_and_isCoAngular F
          left.first).2 ⟨left.first_preStep, leftCoAngular⟩
      letI : IsIso right.first :=
        (birational_isIso_iff_isPreStep_and_isCoAngular F
          right.first).2 ⟨right.first_preStep, rightCoAngular⟩
      let comparison := (asIso left.first).symm ≪≫ asIso right.first
      have firstSquare :
          left.first ≫ comparison.hom = right.first := by
        dsimp only [comparison]
        rw [Iso.trans_hom, Iso.symm_hom]
        simp
      have rightInvSquare :
          right.first ≫ comparison.inv = left.first := by
        rw [← firstSquare, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      have secondSquare :
          comparison.inv ≫ left.second = right.second := by
        apply (cancel_epi right.first).1
        rw [← Category.assoc, rightInvSquare, left.composite,
          right.composite]
      exact
        { midpointIso := comparison
          first_square := firstSquare
          second_square := secondSquare }

/-- A target pre-step-factorization comparison is determined by its
midpoint isomorphism. -/
theorem birational_preStepFactorizationIso_ext
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    {coAngularFirst : Bool}
    {left right : (preFrobenioid F).PreStepFactorization
      arrow coAngularFirst}
    {first second :
      (preFrobenioid F).PreStepFactorizationIso left right}
    (midpointIso : first.midpointIso = second.midpointIso) :
    first = second := by
  cases first
  cases second
  cases midpointIso
  rfl

/-- Definition 1.3(v)(c)'s uniqueness clause in the generic target.  In the
co-angular-first order, the first factor cancels; in the opposite order, the
second factor cancels and determines the inverse comparison. -/
theorem birational_preStepFactorizationIso_unique
    {source target : BirationalCategory F} {arrow : source ⟶ target}
    {coAngularFirst : Bool}
    (left right : (preFrobenioid F).PreStepFactorization
      arrow coAngularFirst)
    (first second :
      (preFrobenioid F).PreStepFactorizationIso left right) :
    first = second := by
  apply birational_preStepFactorizationIso_ext F
  cases coAngularFirst with
  | false =>
      have leftCoAngular :
          (preFrobenioid F).IsCoAngular left.second := by
        exact left.second_kind
      letI : IsIso left.second :=
        (birational_isIso_iff_isPreStep_and_isCoAngular F
          left.second).2 ⟨left.second_preStep, leftCoAngular⟩
      have inverseEquality :
          first.midpointIso.inv = second.midpointIso.inv := by
        apply (cancel_mono left.second).1
        exact first.second_square.trans second.second_square.symm
      apply Iso.ext
      calc
        first.midpointIso.hom =
            first.midpointIso.hom ≫ second.midpointIso.inv ≫
              second.midpointIso.hom := by simp
        _ = first.midpointIso.hom ≫ first.midpointIso.inv ≫
              second.midpointIso.hom := by rw [inverseEquality]
        _ = second.midpointIso.hom := by simp
  | true =>
      have leftCoAngular :
          (preFrobenioid F).IsCoAngular left.first := by
        exact left.first_kind
      letI : IsIso left.first :=
        (birational_isIso_iff_isPreStep_and_isCoAngular F
          left.first).2 ⟨left.first_preStep, leftCoAngular⟩
      apply Iso.ext
      apply (cancel_epi left.first).1
      exact first.first_square.trans second.first_square.symm

/-- Definition 1.3(v)(a) for the generic birational target.  A pre-step roof
has a pre-step source numerator, hence a monic numerator.  The localization
preserves that monomorphism, and the roof differs from it only by the
invertible denominator. -/
theorem birational_preStep_mono
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (arrowPreStep : (preFrobenioid F).IsPreStep arrow) : Mono arrow := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F denominator fraction.f = arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  have numeratorPreStep : F.preFrobenioid.IsPreStep fraction.f :=
    (roofValue_isPreStep_iff F denominator fraction.f).1
      (by rw [roofEquals]; exact arrowPreStep)
  have numeratorMono : Mono fraction.f :=
    F.axioms.preStep_mono fraction.f numeratorPreStep
  have mappedNumeratorMono :
      Mono ((localizationFunctor F).map fraction.f) :=
    localization_map_mono_of_mono F fraction.f numeratorMono
  letI : Mono ((localizationFunctor F).map fraction.f) :=
    mappedNumeratorMono
  have mappedDenominatorIso :
      IsIso ((localizationFunctor F).map denominator.hom) :=
    MorphismProperty.Q_inverts (denominators F) denominator.hom
      denominator.property
  letI : IsIso ((localizationFunctor F).map denominator.hom) :=
    mappedDenominatorIso
  rw [← roofEquals]
  change Mono
    (inv ((localizationFunctor F).map denominator.hom) ≫
      (localizationFunctor F).map fraction.f)
  infer_instance

/-- Definition 1.3(vii)(a) for the generic birational target.  A target roof
into an isotropic object is extended across the source isotropic hull by first
passing through the hull of its numerator domain.  The resulting comparison
arrow between source hulls is a co-angular pre-step, hence a valid target
denominator. -/
def birational_isotropicHull (object : BirationalCategory F) :
    (preFrobenioid F).IsotropicHull object := by
  rcases object with ⟨⟨sourceObject⟩⟩
  let sourceHull := Classical.choice
    (F.axioms.isotropicHull sourceObject)
  refine
    { hull := (localizationFunctor F).obj sourceHull.hull
      hom := (localizationFunctor F).map sourceHull.hom
      preStep :=
        (localization_map_isPreStep_iff F sourceHull.hom).2
          sourceHull.preStep
      isometric := isIsometric F _
      isotropic :=
        (localization_obj_isIsotropic_iff F sourceHull.hull).2
          sourceHull.isotropic
      lift := ?_ }
  intro target arrow targetIsotropic
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let fractionDenominator : CoAngularPreStepOver F sourceObject :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F fractionDenominator fraction.f =
        arrow := by
    change fraction.map (localizationFunctor F)
      (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  have targetObjectIsotropic :
      F.preFrobenioid.IsIsotropic targetObject :=
    (localization_obj_isIsotropic_iff F targetObject).1
      targetIsotropic
  let domainHull := Classical.choice
    (F.axioms.isotropicHull fraction.X')
  let targetLiftExistence := domainHull.lift fraction.f
    targetObjectIsotropic
  let targetLift := Classical.choose targetLiftExistence
  have targetLiftRelation :
      domainHull.hom ≫ targetLift = fraction.f :=
    (Classical.choose_spec targetLiftExistence).1
  let hullLiftExistence := domainHull.lift
    (fraction.s ≫ sourceHull.hom) sourceHull.isotropic
  let hullLift := Classical.choose hullLiftExistence
  have hullLiftRelation :
      domainHull.hom ≫ hullLift =
        fraction.s ≫ sourceHull.hom :=
    (Classical.choose_spec hullLiftExistence).1
  have hullLiftLinear : F.preFrobenioid.IsLinear hullLift := by
    change F.preFrobenioid.frobeniusDegree hullLift = 1
    have degrees := congrArg F.preFrobenioid.frobeniusDegree
      hullLiftRelation
    rw [F.preFrobenioid.frobeniusDegree_comp,
      F.preFrobenioid.frobeniusDegree_comp,
      domainHull.preStep.1, fraction.hs.1.1,
      sourceHull.preStep.1] at degrees
    simpa using degrees
  have hullLiftBaseIso : F.preFrobenioid.IsBaseIso hullLift := by
    have domainHullBaseIso :
        IsIso (F.preFrobenioid.base.map domainHull.hom) :=
      domainHull.preStep.2
    letI : IsIso (F.preFrobenioid.base.map domainHull.hom) :=
      domainHullBaseIso
    have compositeBaseIso : IsIso
        (F.preFrobenioid.base.map (domainHull.hom ≫ hullLift)) := by
      rw [hullLiftRelation, F.preFrobenioid.base.map_comp]
      haveI : IsIso (F.preFrobenioid.base.map fraction.s) :=
        fraction.hs.1.2
      haveI : IsIso (F.preFrobenioid.base.map sourceHull.hom) :=
        sourceHull.preStep.2
      infer_instance
    letI : IsIso
        (F.preFrobenioid.base.map (domainHull.hom ≫ hullLift)) :=
      compositeBaseIso
    change IsIso (F.preFrobenioid.base.map hullLift)
    exact IsIso.of_isIso_fac_left
      (F.preFrobenioid.base.map_comp domainHull.hom hullLift).symm
  have hullLiftCoAngular : F.preFrobenioid.IsCoAngular hullLift :=
    FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F hullLift domainHull.isotropic
  let hullDenominator : CoAngularPreStepOver F sourceHull.hull :=
    { source := domainHull.hull
      hom := hullLift
      property := ⟨⟨hullLiftLinear, hullLiftBaseIso⟩,
        hullLiftCoAngular⟩ }
  let extension := CoAngularPreStepOver.roofValue F hullDenominator
    targetLift
  let extensionSquare : RightOreSquare F hullDenominator.hom
      sourceHull.hom :=
    { source := fraction.X'
      refinement := fraction.s
      refinement_property := fraction.hs
      across := domainHull.hom
      commutes := hullLiftRelation.symm }
  have extensionRelation :
      (localizationFunctor F).map sourceHull.hom ≫ extension = arrow := by
    calc
      (localizationFunctor F).map sourceHull.hom ≫ extension =
          CoAngularPreStepOver.roofValue F fractionDenominator
            (domainHull.hom ≫ targetLift) :=
        localization_map_comp_roofValue F sourceHull.hom
          hullDenominator targetLift extensionSquare
      _ = CoAngularPreStepOver.roofValue F fractionDenominator
          fraction.f := by rw [targetLiftRelation]
      _ = arrow := roofEquals
  refine ⟨extension, extensionRelation, ?_⟩
  intro candidate candidateRelation
  have mappedHullEpi : Epi
      ((localizationFunctor F).map sourceHull.hom) :=
    localization_map_epi F sourceHull.hom
  letI : Epi ((localizationFunctor F).map sourceHull.hom) :=
    mappedHullEpi
  apply (cancel_epi ((localizationFunctor F).map sourceHull.hom)).1
  exact candidateRelation.trans extensionRelation.symm

/-- Definition 1.3(vii)(b) for the generic birational target.  A right
fraction first moves backward along its co-angular linear denominator, where
isotropicity is invariant, and then forward along its source numerator, where
the source Frobenioid's target-closure axiom applies. -/
theorem birational_isotropic_closedUnderTargets
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (sourceIsotropic : (preFrobenioid F).IsIsotropic source) :
    (preFrobenioid F).IsIsotropic target := by
  rcases source with ⟨⟨sourceObject⟩⟩
  rcases target with ⟨⟨targetObject⟩⟩
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, _represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  have sourceObjectIsotropic :
      F.preFrobenioid.IsIsotropic sourceObject :=
    (localization_obj_isIsotropic_iff F sourceObject).1 sourceIsotropic
  have fractionSourceIsotropic :
      F.preFrobenioid.IsIsotropic fraction.X' :=
    (FrobenioidRationalMonoidTransport.isIsotropic_source_iff_target_of_coAngular_linear
        F fraction.s fraction.hs.2 fraction.hs.1.1).2
      sourceObjectIsotropic
  change (preFrobenioid F).IsIsotropic
    ((localizationFunctor F).obj targetObject)
  exact (localization_obj_isIsotropic_iff F targetObject).2
    (F.axioms.isotropic_closedUnderTargets fraction.f
      fractionSourceIsotropic)

/-- Proposition 1.4(i) in the generic birational target: every arrow out of
an isotropic object is co-angular. -/
theorem birational_isCoAngular_of_isotropicSource
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (sourceIsotropic : (preFrobenioid F).IsIsotropic source) :
    (preFrobenioid F).IsCoAngular arrow := by
  intro U V gamma beta alpha _ _ betaPreStep betaIsometric _
  exact birational_isotropic_closedUnderTargets F gamma sourceIsotropic
    beta betaPreStep betaIsometric

/-- The Proposition 2.2 base-isomorphism bridge in the generic target.
Between isotropic target objects, every base isomorphism is represented by
a target isomorphism with exactly that base coordinate. -/
theorem birational_iso_over_baseIso_of_isotropic
    (left right : BirationalCategory F)
    (leftIsotropic : (preFrobenioid F).IsIsotropic left)
    (rightIsotropic : (preFrobenioid F).IsIsotropic right)
    (baseIso : (preFrobenioid F).base.obj left ≅
      (preFrobenioid F).base.obj right) :
    ∃ targetIso : left ≅ right,
      (preFrobenioid F).base.map targetIso.hom = baseIso.hom := by
  let common := birational_commonPreSteps F left right baseIso
  let hull := birational_isotropicHull F common.midpoint
  obtain ⟨toLeft, toLeftRelation, _⟩ :=
    hull.lift common.toLeft leftIsotropic
  obtain ⟨toRight, toRightRelation, _⟩ :=
    hull.lift common.toRight rightIsotropic
  have toLeftLinear : (preFrobenioid F).IsLinear toLeft := by
    change (preFrobenioid F).frobeniusDegree toLeft = 1
    have degrees := congrArg (preFrobenioid F).frobeniusDegree
      toLeftRelation
    rw [(preFrobenioid F).frobeniusDegree_comp,
      hull.preStep.1, common.toLeft_preStep.1] at degrees
    simpa using degrees
  have toRightLinear : (preFrobenioid F).IsLinear toRight := by
    change (preFrobenioid F).frobeniusDegree toRight = 1
    have degrees := congrArg (preFrobenioid F).frobeniusDegree
      toRightRelation
    rw [(preFrobenioid F).frobeniusDegree_comp,
      hull.preStep.1, common.toRight_preStep.1] at degrees
    simpa using degrees
  have toLeftBaseIso : (preFrobenioid F).IsBaseIso toLeft := by
    change IsIso ((preFrobenioid F).base.map toLeft)
    have compositeIsIso : IsIso
        ((preFrobenioid F).base.map hull.hom ≫
          (preFrobenioid F).base.map toLeft) := by
      rw [← (preFrobenioid F).base.map_comp, toLeftRelation]
      exact common.toLeft_preStep.2
    haveI : IsIso
        ((preFrobenioid F).base.map hull.hom ≫
          (preFrobenioid F).base.map toLeft) := compositeIsIso
    haveI : IsIso ((preFrobenioid F).base.map hull.hom) :=
      hull.preStep.2
    exact IsIso.of_isIso_comp_left
      ((preFrobenioid F).base.map hull.hom)
      ((preFrobenioid F).base.map toLeft)
  have toRightBaseIso : (preFrobenioid F).IsBaseIso toRight := by
    change IsIso ((preFrobenioid F).base.map toRight)
    have compositeIsIso : IsIso
        ((preFrobenioid F).base.map hull.hom ≫
          (preFrobenioid F).base.map toRight) := by
      rw [← (preFrobenioid F).base.map_comp, toRightRelation]
      exact common.toRight_preStep.2
    haveI : IsIso
        ((preFrobenioid F).base.map hull.hom ≫
          (preFrobenioid F).base.map toRight) := compositeIsIso
    haveI : IsIso ((preFrobenioid F).base.map hull.hom) :=
      hull.preStep.2
    exact IsIso.of_isIso_comp_left
      ((preFrobenioid F).base.map hull.hom)
      ((preFrobenioid F).base.map toRight)
  have toLeftPreStep : (preFrobenioid F).IsPreStep toLeft :=
    ⟨toLeftLinear, toLeftBaseIso⟩
  have toRightPreStep : (preFrobenioid F).IsPreStep toRight :=
    ⟨toRightLinear, toRightBaseIso⟩
  have toLeftCoAngular : (preFrobenioid F).IsCoAngular toLeft :=
    birational_isCoAngular_of_isotropicSource F toLeft hull.isotropic
  have toRightCoAngular : (preFrobenioid F).IsCoAngular toRight :=
    birational_isCoAngular_of_isotropicSource F toRight hull.isotropic
  have toLeftIsIso : IsIso toLeft :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F toLeft).2
      ⟨toLeftPreStep, toLeftCoAngular⟩
  have toRightIsIso : IsIso toRight :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F toRight).2
      ⟨toRightPreStep, toRightCoAngular⟩
  letI : IsIso toLeft := toLeftIsIso
  letI : IsIso toRight := toRightIsIso
  letI : IsIso ((preFrobenioid F).base.map hull.hom) :=
    hull.preStep.2
  let targetIso := (asIso toLeft).symm ≪≫ asIso toRight
  refine ⟨targetIso, ?_⟩
  have leftBaseRelation := congrArg (preFrobenioid F).base.map
    toLeftRelation
  have rightBaseRelation := congrArg (preFrobenioid F).base.map
    toRightRelation
  rw [(preFrobenioid F).base.map_comp] at leftBaseRelation rightBaseRelation
  have rightBaseViaLeft :
      (preFrobenioid F).base.map toRight =
        (preFrobenioid F).base.map toLeft ≫ baseIso.hom := by
    apply (cancel_epi ((preFrobenioid F).base.map hull.hom)).1
    calc
      (preFrobenioid F).base.map hull.hom ≫
            (preFrobenioid F).base.map toRight =
          (preFrobenioid F).base.map common.toRight :=
        rightBaseRelation
      _ = ((preFrobenioid F).base.map common.toLeft ≫
            common.leftBaseInverse) ≫
          (preFrobenioid F).base.map common.toRight := by
        rw [common.hom_leftBaseInverse, Category.id_comp]
      _ = (preFrobenioid F).base.map common.toLeft ≫
          (common.leftBaseInverse ≫
            (preFrobenioid F).base.map common.toRight) :=
        Category.assoc _ _ _
      _ = (preFrobenioid F).base.map common.toLeft ≫
          baseIso.hom := by rw [common.comparison]
      _ = ((preFrobenioid F).base.map hull.hom ≫
            (preFrobenioid F).base.map toLeft) ≫ baseIso.hom := by
        rw [leftBaseRelation]
      _ = (preFrobenioid F).base.map hull.hom ≫
          ((preFrobenioid F).base.map toLeft ≫ baseIso.hom) :=
        Category.assoc _ _ _
  change (preFrobenioid F).base.map (inv toLeft ≫ toRight) =
    baseIso.hom
  rw [(preFrobenioid F).base.map_comp, Functor.map_inv,
    rightBaseViaLeft, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

/-- A chosen isotropic object of the birational target over a prescribed
base object.  The choice is made by taking an isotropic hull of any object
provided by Definition 1.3(i)(a). -/
structure BirationalIsotropicBaseRepresentative
    (baseObject : F.baseCategory) where
  object : F.carrier
  isotropic : (preFrobenioid F).IsIsotropic
    ((localizationFunctor F).obj object)
  baseIso : F.preFrobenioid.base.obj object ≅ baseObject

/-- Every base object admits an isotropic representative in the generic
birational target. -/
def birationalIsotropicBaseRepresentative
    (baseObject : F.baseCategory) :
    BirationalIsotropicBaseRepresentative F baseObject := by
  let represented := Classical.choose
    (F.axioms.baseRepresented baseObject)
  have representedProperty := Classical.choose_spec
    (F.axioms.baseRepresented baseObject)
  let baseIso := Classical.choice representedProperty.2
  let object := represented
  let hull := Classical.choice (F.axioms.isotropicHull object)
  have mappedHullIso : IsIso
      (F.preFrobenioid.base.map hull.hom) := hull.preStep.2
  letI : IsIso (F.preFrobenioid.base.map hull.hom) := mappedHullIso
  exact
    { object := hull.hull
      isotropic := (localization_obj_isIsotropic_iff F hull.hull).2
        hull.isotropic
      baseIso :=
        (asIso (F.preFrobenioid.base.map hull.hom)).symm ≪≫ baseIso }

/-- Isotropicity reflects across a co-angular linear arrow in the generic
birational target.  This is Frobenioids I, Proposition 1.9(iv), applied after
the target axioms have been constructed directly. -/
theorem birational_isIsotropic_source_of_coAngular_linear
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (coAngular : (preFrobenioid F).IsCoAngular arrow)
    (linear : (preFrobenioid F).IsLinear arrow)
    (targetIsotropic : (preFrobenioid F).IsIsotropic target) :
    (preFrobenioid F).IsIsotropic source := by
  let hull := birational_isotropicHull F source
  obtain ⟨extension, relation, _unique⟩ :=
    hull.lift arrow targetIsotropic
  have extensionLinear : (preFrobenioid F).IsLinear extension := by
    change (preFrobenioid F).frobeniusDegree extension = 1
    have degrees := congrArg (preFrobenioid F).frobeniusDegree relation
    rw [(preFrobenioid F).frobeniusDegree_comp,
      hull.preStep.1, linear] at degrees
    simpa using degrees
  have hullIso : IsIso hull.hom := by
    apply coAngular (𝟙 source) hull.hom extension
    · simpa only [Category.id_comp] using relation
    · exact extensionLinear
    · exact hull.preStep
    · exact hull.isometric
    · right
      change IsIso ((preFrobenioid F).base.map (𝟙 source))
      infer_instance
  letI : IsIso hull.hom := hullIso
  intro other next preStep isometric
  exact (birational_isotropic_closedUnderTargets F
    (source := hull.hull) (target := source) (inv hull.hom) hull.isotropic)
      next preStep isometric

/-- A Frobenius-degree witness, returned to an isotropic object along an
isomorphism with inverse base coordinate, supplies a base-identity
degree-two endomorphism. -/
def birationalIsotropicDegreeTwoEndomorphism
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) : object ⟶ object := by
  let witness := birational_frobeniusDegree F object 2
  have codomainIsotropic :
      (preFrobenioid F).IsIsotropic witness.codomain :=
    birational_isotropic_closedUnderTargets F witness.hom isotropic
  have baseMapIsIso : IsIso ((preFrobenioid F).base.map witness.hom) :=
    witness.ofFrobeniusType.2
  letI : IsIso ((preFrobenioid F).base.map witness.hom) := baseMapIsIso
  let returnExistence := birational_iso_over_baseIso_of_isotropic F
    witness.codomain object codomainIsotropic isotropic
      (asIso ((preFrobenioid F).base.map witness.hom)).symm
  let returnIso := Classical.choose returnExistence
  exact witness.hom ≫ returnIso.hom

theorem birationalIsotropicDegreeTwoEndomorphism_baseIdentity
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) :
    (preFrobenioid F).IsBaseIdentity
      (birationalIsotropicDegreeTwoEndomorphism F object isotropic) := by
  let witness := birational_frobeniusDegree F object 2
  have codomainIsotropic :
      (preFrobenioid F).IsIsotropic witness.codomain :=
    birational_isotropic_closedUnderTargets F witness.hom isotropic
  have baseMapIsIso : IsIso ((preFrobenioid F).base.map witness.hom) :=
    witness.ofFrobeniusType.2
  letI : IsIso ((preFrobenioid F).base.map witness.hom) := baseMapIsIso
  let returnExistence := birational_iso_over_baseIso_of_isotropic F
    witness.codomain object codomainIsotropic isotropic
      (asIso ((preFrobenioid F).base.map witness.hom)).symm
  let returnIso := Classical.choose returnExistence
  have returnBase := Classical.choose_spec returnExistence
  change (preFrobenioid F).base.map (witness.hom ≫ returnIso.hom) = 𝟙 _
  rw [(preFrobenioid F).base.map_comp, returnBase]
  simp

theorem birationalIsotropicDegreeTwoEndomorphism_degree
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) :
    (preFrobenioid F).frobeniusDegree
      (birationalIsotropicDegreeTwoEndomorphism F object isotropic) = 2 := by
  let witness := birational_frobeniusDegree F object 2
  have codomainIsotropic :
      (preFrobenioid F).IsIsotropic witness.codomain :=
    birational_isotropic_closedUnderTargets F witness.hom isotropic
  have baseMapIsIso : IsIso ((preFrobenioid F).base.map witness.hom) :=
    witness.ofFrobeniusType.2
  letI : IsIso ((preFrobenioid F).base.map witness.hom) := baseMapIsIso
  let returnExistence := birational_iso_over_baseIso_of_isotropic F
    witness.codomain object codomainIsotropic isotropic
      (asIso ((preFrobenioid F).base.map witness.hom)).symm
  let returnIso := Classical.choose returnExistence
  have returnLinear : (preFrobenioid F).IsLinear returnIso.hom :=
    (birational_isPreStep_of_isIso F returnIso.hom (by infer_instance)).1
  change (preFrobenioid F).frobeniusDegree
      (witness.hom ≫ returnIso.hom) = 2
  rw [(preFrobenioid F).frobeniusDegree_comp,
    witness.degree, returnLinear]
  rfl

/-- The corrected Proposition 4.4(ii) square-law argument.  On an isotropic,
Frobenius-normalized target object, normalization by a degree-two
base-identity endomorphism gives `(alpha * beta)^2 = alpha^2 * beta^2`;
cancellation then makes the rational-function group commutative. -/
theorem birational_linearBaseIdentityEndomorphism_commutes_of_isotropic
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object)
    (normalized : (preFrobenioid F).IsFrobeniusNormalized object)
    (left right :
      (preFrobenioid F).LinearBaseIdentityEndomorphism object) :
    left.hom ≫ right.hom = right.hom ≫ left.hom := by
  let phi := birationalIsotropicDegreeTwoEndomorphism F object isotropic
  have phiBaseIdentity : (preFrobenioid F).IsBaseIdentity phi :=
    birationalIsotropicDegreeTwoEndomorphism_baseIdentity F object isotropic
  have phiDegree : (preFrobenioid F).frobeniusDegree phi = 2 :=
    birationalIsotropicDegreeTwoEndomorphism_degree F object isotropic
  have productNormalization := normalized phi phiBaseIdentity (left * right)
  have leftNormalization := normalized phi phiBaseIdentity left
  have rightNormalization := normalized phi phiBaseIdentity right
  have productNormalizationHom :
      phi ≫ ((left.hom ≫ right.hom) ≫
          (left.hom ≫ right.hom)) =
        (left.hom ≫ right.hom) ≫ phi := by
    simpa only [phiDegree, PNat.val_ofNat, pow_two] using
      productNormalization
  have leftNormalizationHom :
      phi ≫ (left.hom ≫ left.hom) = left.hom ≫ phi := by
    simpa only [phiDegree, PNat.val_ofNat, pow_two] using
      leftNormalization
  have rightNormalizationHom :
      phi ≫ (right.hom ≫ right.hom) = right.hom ≫ phi := by
    simpa only [phiDegree, PNat.val_ofNat, pow_two] using
      rightNormalization
  letI : Epi phi := birational_totallyEpimorphic F phi
  have squareLaw :
      (left.hom ≫ right.hom) ≫ (left.hom ≫ right.hom) =
        (left.hom ≫ left.hom) ≫ (right.hom ≫ right.hom) := by
    apply (cancel_epi phi).1
    calc
      phi ≫ ((left.hom ≫ right.hom) ≫
          (left.hom ≫ right.hom)) =
          (left.hom ≫ right.hom) ≫ phi := by
        exact productNormalizationHom
      _ = left.hom ≫ (right.hom ≫ phi) := by
        simp only [Category.assoc]
      _ = left.hom ≫ (phi ≫ (right.hom ≫ right.hom)) := by
        rw [← rightNormalizationHom]
      _ = (left.hom ≫ phi) ≫ (right.hom ≫ right.hom) := by
        simp only [Category.assoc]
      _ = (phi ≫ (left.hom ≫ left.hom)) ≫
          (right.hom ≫ right.hom) := by
        rw [← leftNormalizationHom]
      _ = phi ≫ ((left.hom ≫ left.hom) ≫
          (right.hom ≫ right.hom)) := by
        simp only [Category.assoc]
  letI : IsIso left.hom :=
    birational_linearBaseIdentityEndomorphism_isIso F left
  letI : IsIso right.hom :=
    birational_linearBaseIdentityEndomorphism_isIso F right
  have reverse : right.hom ≫ left.hom = left.hom ≫ right.hom := by
    apply (cancel_epi left.hom).1
    apply (cancel_mono right.hom).1
    simpa only [Category.assoc] using squareLaw
  exact reverse.symm

/-- The official correction to Proposition 4.4(ii): birational Frobenius
normalization makes all target rational-function groups commutative.  The
arbitrary object embeds into its isotropic hull, where the square-law argument
applies. -/
theorem birational_linearBaseIdentityEndomorphism_commutes
    (hypothesis : F.preFrobenioid.IsBirationallyFrobeniusNormalizedType
      (preFrobenioid F) (localizationFunctor F))
    {object : BirationalCategory F}
    (left right :
      (preFrobenioid F).LinearBaseIdentityEndomorphism object) :
    left.hom ≫ right.hom = right.hom ≫ left.hom := by
  let hull := birational_isotropicHull F object
  let leftExtension := birationalHullEndomorphism F hull left
  let rightExtension := birationalHullEndomorphism F hull right
  have hullNormalized :
      (preFrobenioid F).IsFrobeniusNormalized hull.hull := by
    rcases hull.hull with ⟨⟨hullSource⟩⟩
    exact hypothesis hullSource
  have extensionsCommute :
      leftExtension.hom ≫ rightExtension.hom =
        rightExtension.hom ≫ leftExtension.hom :=
    birational_linearBaseIdentityEndomorphism_commutes_of_isotropic F
      hull.hull hull.isotropic
        hullNormalized leftExtension rightExtension
  haveI : Mono hull.hom := birational_preStep_mono F hull.hom hull.preStep
  apply (cancel_mono hull.hom).1
  calc
    (left.hom ≫ right.hom) ≫ hull.hom =
        left.hom ≫ (right.hom ≫ hull.hom) := Category.assoc _ _ _
    _ = left.hom ≫ (hull.hom ≫ rightExtension.hom) := by
      rw [birationalHullEndomorphism_relation F hull right]
    _ = (left.hom ≫ hull.hom) ≫ rightExtension.hom :=
      (Category.assoc _ _ _).symm
    _ = (hull.hom ≫ leftExtension.hom) ≫
        rightExtension.hom := by
      rw [birationalHullEndomorphism_relation F hull left]
    _ = hull.hom ≫ (leftExtension.hom ≫ rightExtension.hom) :=
      Category.assoc _ _ _
    _ = hull.hom ≫ (rightExtension.hom ≫ leftExtension.hom) := by
      rw [extensionsCommute]
    _ = (hull.hom ≫ rightExtension.hom) ≫
        leftExtension.hom := (Category.assoc _ _ _).symm
    _ = (right.hom ≫ hull.hom) ≫ leftExtension.hom := by
      rw [birationalHullEndomorphism_relation F hull right]
    _ = right.hom ≫ (hull.hom ≫ leftExtension.hom) :=
      Category.assoc _ _ _
    _ = right.hom ≫ (left.hom ≫ hull.hom) := by
      rw [birationalHullEndomorphism_relation F hull left]
    _ = (right.hom ≫ left.hom) ≫ hull.hom :=
      (Category.assoc _ _ _).symm

/-- Under the corrected birational Frobenius-normalization hypothesis,
unit transport depends only on the induced base arrow.  Two co-angular
pre-steps with the same base differ by a target rational function; the
commutativity theorem above makes conjugation by that difference trivial. -/
theorem birational_unitTransport_dependsOnlyOnBase
    (hypothesis : F.preFrobenioid.IsBirationallyFrobeniusNormalizedType
      (preFrobenioid F) (localizationFunctor F))
    {source target : BirationalCategory F} (left right : source ⟶ target)
    (leftPreStep : (preFrobenioid F).IsPreStep left)
    (leftCoAngular : (preFrobenioid F).IsCoAngular left)
    (rightPreStep : (preFrobenioid F).IsPreStep right)
    (rightCoAngular : (preFrobenioid F).IsCoAngular right)
    (baseEquality : (preFrobenioid F).base.map left =
      (preFrobenioid F).base.map right) :
    (birational_unitTransport F left leftPreStep leftCoAngular).transport =
      (birational_unitTransport F right rightPreStep rightCoAngular).transport := by
  have leftIsIso : IsIso left :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F left).2
      ⟨leftPreStep, leftCoAngular⟩
  have rightIsIso : IsIso right :=
    (birational_isIso_iff_isPreStep_and_isCoAngular F right).2
      ⟨rightPreStep, rightCoAngular⟩
  letI : IsIso left := leftIsIso
  letI : IsIso right := rightIsIso
  let correction :
      (preFrobenioid F).LinearBaseIdentityEndomorphism target :=
    { hom := inv left ≫ right
      linear := by
        rw [PreFrobenioid.IsLinear,
          (preFrobenioid F).frobeniusDegree_comp,
          (birational_isPreStep_of_isIso F (inv left) inferInstance).1,
          rightPreStep.1]
        rfl
      baseIdentity := by
        rw [PreFrobenioid.IsBaseIdentity,
          (preFrobenioid F).base.map_comp]
        rw [← baseEquality, ← (preFrobenioid F).base.map_comp]
        simp }
  let leftTransport :=
    birational_unitTransport F left leftPreStep leftCoAngular
  let rightTransport :=
    birational_unitTransport F right rightPreStep rightCoAngular
  apply MulEquiv.ext
  intro value
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  have leftConjugates :
      value.hom ≫ left = left ≫ (leftTransport.transport value).hom :=
    leftTransport.conjugates value
  have rightConjugates :
      value.hom ≫ right = right ≫ (rightTransport.transport value).hom :=
    rightTransport.conjugates value
  have transportCorrection :
      (leftTransport.transport value).hom ≫ correction.hom =
        correction.hom ≫ (rightTransport.transport value).hom := by
    apply (cancel_epi left).1
    calc
      left ≫ ((leftTransport.transport value).hom ≫ correction.hom) =
          (left ≫ (leftTransport.transport value).hom) ≫ correction.hom :=
        (Category.assoc _ _ _).symm
      _ = (value.hom ≫ left) ≫ correction.hom := by
        rw [leftConjugates]
      _ = value.hom ≫ (left ≫ correction.hom) :=
        Category.assoc _ _ _
      _ = value.hom ≫ right := by
        simp [correction]
      _ = right ≫ (rightTransport.transport value).hom :=
        rightConjugates
      _ = (left ≫ correction.hom) ≫
          (rightTransport.transport value).hom := by
        simp [correction]
      _ = left ≫ (correction.hom ≫
          (rightTransport.transport value).hom) :=
        Category.assoc _ _ _
  have correctionCommutes :
      (leftTransport.transport value).hom ≫ correction.hom =
        correction.hom ≫ (leftTransport.transport value).hom :=
    birational_linearBaseIdentityEndomorphism_commutes F hypothesis
      (leftTransport.transport value) correction
  haveI : IsIso correction.hom :=
    birational_linearBaseIdentityEndomorphism_isIso F correction
  apply (cancel_epi correction.hom).1
  exact correctionCommutes.symm.trans transportCorrection

/-- The unconditional part of the corrected Proposition 4.4(ii): the generic
birational target is a connected, totally epimorphic group-like
pre-Frobenioid.  Faithfulness of its canonical localization is the separate
theorem `localizationFunctor_faithful`. -/
def birational_preFrobenioidPresentation :
    PreFrobenioidPresentation where
  carrier := Cat.of (BirationalCategory F)
  baseCategory := Cat.of F.baseCategory
  isFSM := F.isFSM
  preFrobenioid := preFrobenioid F
  carrierConnected := birationalCategory_isConnected F
  baseConnected := F.baseConnected
  carrierTotallyEpimorphic := birational_totallyEpimorphic F
  baseTotallyEpimorphic := F.baseTotallyEpimorphic

/-- The conditional part of the corrected Proposition 4.4(ii): the generic
birational pre-Frobenioid satisfies all seven axiom groups when the source is
of birationally Frobenius-normalized type. -/
def birational_frobenioidAxioms
    (hypothesis : F.preFrobenioid.IsBirationallyFrobeniusNormalizedType
      (preFrobenioid F) (localizationFunctor F)) :
    (preFrobenioid F).FrobenioidAxioms where
  baseRepresented := birational_baseRepresented F
  commonPreSteps left right baseIso :=
    ⟨birational_commonPreSteps F left right baseIso⟩
  pullbackBaseSlices := birational_pullbackBaseSlices F
  frobeniusDegree := birational_frobeniusDegree F
  coAngular_comp := birational_coAngular_comp F
  coAngular_parallelToCoAngularPreStep :=
    birational_coAngular_parallelToCoAngularPreStep F
  unitTransport := birational_unitTransport F
  unitTransport_unique := birational_unitTransport_unique F
  unitTransport_dependsOnlyOnBase left right leftPre leftCo rightPre
      rightCo equality :=
    birational_unitTransport_dependsOnlyOnBase F hypothesis left right
      leftPre leftCo rightPre rightCo equality
  outgoingDivisorRepresentative := birational_outgoingDivisorRepresentative F
  outgoingDivisorOrderFullyFaithful :=
    birational_outgoingDivisorOrderFullyFaithful F
  outgoingDivisorRepresentative_unique :=
    birational_outgoingDivisorRepresentative_unique F
  incomingDivisor arrow _ _ := birational_incomingDivisor F arrow
  incomingDivisorRepresentative :=
    birational_incomingDivisorRepresentative F
  incomingDivisorOrderFullyFaithful :=
    birational_incomingDivisorOrderFullyFaithful F
  incomingDivisorRepresentative_unique :=
    birational_incomingDivisorRepresentative_unique F
  factorization arrow := birational_factorization F arrow
  pullback_linear_lbInvertible := birational_pullback_linear_lbInvertible F
  factorizationIso := birational_factorizationIso F
  factorizationIso_unique := birational_factorizationIso_unique F
  preStep_mono := birational_preStep_mono F
  preStep_coAngularThenIsometric :=
    birational_preStep_coAngularThenIsometric F
  preStep_isometricThenCoAngular :=
    birational_preStep_isometricThenCoAngular F
  preStepFactorizationIso := birational_preStepFactorizationIso F
  preStepFactorizationIso_unique :=
    birational_preStepFactorizationIso_unique F
  faithfulUpToUnits := birational_faithfulUpToUnits F
  isotropicHull object := ⟨birational_isotropicHull F object⟩
  isotropic_closedUnderTargets := birational_isotropic_closedUnderTargets F

/-- The generic birational category as a full Frobenioid presentation under
the precise additional hypothesis in the corrected Proposition 4.4(ii). -/
def birational_frobenioidPresentation
    (hypothesis : F.preFrobenioid.IsBirationallyFrobeniusNormalizedType
    (preFrobenioid F) (localizationFunctor F)) :
    FrobenioidPresentation where
  toPreFrobenioidPresentation := birational_preFrobenioidPresentation F
  axioms := birational_frobenioidAxioms F hypothesis

/-- A contravariant subgroup family inside the groupification of the source
divisorial monoid.  This is the generic ambient type of `Phi^birat`. -/
@[ext]
structure BirationalDivisorSubfunctor where
  obj : ∀ baseObject : F.baseCategory,
    AddSubgroup
      (Algebra.GrothendieckAddGroup
        (F.preFrobenioid.divisorMonoid.obj baseObject).carrier)
  pullback_mem :
    ∀ {source target : F.baseCategory} (arrow : source ⟶ target)
      {divisor : Algebra.GrothendieckAddGroup
        (F.preFrobenioid.divisorMonoid.obj target).carrier},
      divisor ∈ obj target →
      F.preFrobenioid.divisorMonoid.gpPullback arrow divisor ∈
          obj source

namespace BirationalDivisorSubfunctor

/-- Pull-back restricted to a generic birational divisor subfunctor. -/
def pullback (candidate : BirationalDivisorSubfunctor F)
    {source target : F.baseCategory} (arrow : source ⟶ target) :
    candidate.obj target →+ candidate.obj source where
  toFun divisor :=
    ⟨F.preFrobenioid.divisorMonoid.gpPullback arrow divisor.1,
      candidate.pullback_mem arrow divisor.property⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' left right := by
    apply Subtype.ext
    exact map_add _ left.1 right.1

@[simp]
theorem pullback_coe (candidate : BirationalDivisorSubfunctor F)
    {source target : F.baseCategory} (arrow : source ⟶ target)
    (divisor : candidate.obj target) :
    ((candidate.pullback F arrow divisor : candidate.obj source) :
        Algebra.GrothendieckAddGroup
          (F.preFrobenioid.divisorMonoid.obj source).carrier) =
      F.preFrobenioid.divisorMonoid.gpPullback arrow divisor.1 :=
  rfl

theorem pullback_id (candidate : BirationalDivisorSubfunctor F)
    (object : F.baseCategory) :
    candidate.pullback F (𝟙 object) =
      AddMonoidHom.id (candidate.obj object) := by
  apply AddMonoidHom.ext
  intro divisor
  apply Subtype.ext
  rw [pullback_coe, F.preFrobenioid.divisorMonoid.gpPullback_id]
  rfl

theorem pullback_comp (candidate : BirationalDivisorSubfunctor F)
    {source middle target : F.baseCategory}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    candidate.pullback F (first ≫ second) =
      (candidate.pullback F first).comp (candidate.pullback F second) := by
  apply AddMonoidHom.ext
  intro divisor
  apply Subtype.ext
  change F.preFrobenioid.divisorMonoid.gpPullback
      (first ≫ second) divisor.1 =
    F.preFrobenioid.divisorMonoid.gpPullback first
      (F.preFrobenioid.divisorMonoid.gpPullback second divisor.1)
  rw [F.preFrobenioid.divisorMonoid.gpPullback_comp]
  rfl

end BirationalDivisorSubfunctor

/-- An arrow of the elementary category attached to a subgroup family
`Psi ⊆ Phi^gp`. -/
@[ext]
structure RestrictedGroupifiedElementaryHom
    (candidate : BirationalDivisorSubfunctor F)
    (source target : F.baseCategory) where
  base : source ⟶ target
  divisor : candidate.obj source
  frobeniusDegree : ℕ+

namespace RestrictedGroupifiedElementaryHom

def id (candidate : BirationalDivisorSubfunctor F)
    (object : F.baseCategory) :
    RestrictedGroupifiedElementaryHom F candidate object object where
  base := 𝟙 object
  divisor := 0
  frobeniusDegree := 1

def comp (candidate : BirationalDivisorSubfunctor F)
    {source middle target : F.baseCategory}
    (first : RestrictedGroupifiedElementaryHom F candidate source middle)
    (second : RestrictedGroupifiedElementaryHom F candidate middle target) :
    RestrictedGroupifiedElementaryHom F candidate source target where
  base := first.base ≫ second.base
  divisor := candidate.pullback F first.base second.divisor +
    second.frobeniusDegree.1 • first.divisor
  frobeniusDegree := first.frobeniusDegree * second.frobeniusDegree

end RestrictedGroupifiedElementaryHom

/-- The restricted elementary category `F_Psi` for a generic subgroup family
`Psi ⊆ Phi^gp`. -/
@[ext]
structure RestrictedGroupifiedElementaryFrobenioid
    (_candidate : BirationalDivisorSubfunctor F) where
  base : F.baseCategory

namespace RestrictedGroupifiedElementaryFrobenioid

instance (candidate : BirationalDivisorSubfunctor F) :
    Category.{u} (RestrictedGroupifiedElementaryFrobenioid F candidate) where
  Hom source target :=
    RestrictedGroupifiedElementaryHom F candidate source.base target.base
  id object := RestrictedGroupifiedElementaryHom.id F candidate object.base
  comp first second :=
    RestrictedGroupifiedElementaryHom.comp F candidate first second
  id_comp arrow := by
    ext
    · simp [RestrictedGroupifiedElementaryHom.comp,
        RestrictedGroupifiedElementaryHom.id]
    · change F.preFrobenioid.divisorMonoid.gpPullback (𝟙 _)
          arrow.divisor.1 + arrow.frobeniusDegree.1 • 0 =
        arrow.divisor.1
      rw [F.preFrobenioid.divisorMonoid.gpPullback_id]
      simp
    · simp [RestrictedGroupifiedElementaryHom.comp,
        RestrictedGroupifiedElementaryHom.id]
  comp_id arrow := by
    ext
    · simp [RestrictedGroupifiedElementaryHom.comp,
        RestrictedGroupifiedElementaryHom.id]
    · change F.preFrobenioid.divisorMonoid.gpPullback arrow.base 0 +
          1 • arrow.divisor.1 = arrow.divisor.1
      rw [map_zero, zero_add, one_nsmul]
    · simp [RestrictedGroupifiedElementaryHom.comp,
        RestrictedGroupifiedElementaryHom.id]
  assoc first second third := by
    ext
    · simp [RestrictedGroupifiedElementaryHom.comp, Category.assoc]
    · change
        F.preFrobenioid.divisorMonoid.gpPullback
              (first.base ≫ second.base) third.divisor.1 +
            third.frobeniusDegree.1 •
              (F.preFrobenioid.divisorMonoid.gpPullback
                  first.base second.divisor.1 +
                second.frobeniusDegree.1 • first.divisor.1) =
          F.preFrobenioid.divisorMonoid.gpPullback first.base
              (F.preFrobenioid.divisorMonoid.gpPullback
                  second.base third.divisor.1 +
                third.frobeniusDegree.1 • second.divisor.1) +
            (second.frobeniusDegree.1 * third.frobeniusDegree.1) •
              first.divisor.1
      rw [F.preFrobenioid.divisorMonoid.gpPullback_comp]
      simp [nsmul_add, mul_nsmul, add_assoc]
    · simp [RestrictedGroupifiedElementaryHom.comp, mul_assoc]

/-- Inclusion `F_Psi → F_(Phi^gp)` induced by the subgroup embeddings. -/
def inclusion (candidate : BirationalDivisorSubfunctor F) :
    RestrictedGroupifiedElementaryFrobenioid F candidate ⥤
      GroupifiedElementaryFrobenioid
        F.preFrobenioid.divisorMonoid where
  obj object := ⟨object.base⟩
  map arrow :=
    { base := arrow.base
      divisor := arrow.divisor.1
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := rfl
  map_comp first second := by
    apply GroupifiedElementaryHom.ext
    · rfl
    · rfl
    · rfl

/-- The elementary inclusion of a generic divisor subgroup is faithful. -/
theorem inclusion_faithful (candidate : BirationalDivisorSubfunctor F) :
    (inclusion F candidate).Faithful := by
  constructor
  intro source target first second equality
  apply RestrictedGroupifiedElementaryHom.ext
  · simpa only [inclusion] using
      congrArg GroupifiedElementaryHom.base equality
  · apply Subtype.ext
    simpa only [inclusion] using
      congrArg GroupifiedElementaryHom.divisor equality
  · simpa only [inclusion] using
      congrArg GroupifiedElementaryHom.frobeniusDegree equality

end RestrictedGroupifiedElementaryFrobenioid

/-- The base-indexed birational divisor range.  A divisor belongs at `B`
when its pull-back to the chosen isotropic representative over `B` is the
divisor of a target rational function. -/
def birationalBaseDivisorRange (baseObject : F.baseCategory) :
    AddSubgroup
      (Algebra.GrothendieckAddGroup
        (F.preFrobenioid.divisorMonoid.obj baseObject).carrier) :=
  let representative := birationalIsotropicBaseRepresentative F baseObject
  (birationalDivisorRange F representative.object).comap
    (F.preFrobenioid.divisorMonoid.gpPullback
      representative.baseIso.hom)

/-- Membership in the base-indexed range is membership after transport to
the chosen isotropic representative. -/
theorem mem_birationalBaseDivisorRange_iff
    (baseObject : F.baseCategory)
    (divisor : Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj baseObject).carrier) :
    divisor ∈ birationalBaseDivisorRange F baseObject ↔
      F.preFrobenioid.divisorMonoid.gpPullback
          (birationalIsotropicBaseRepresentative F baseObject).baseIso.hom
          divisor ∈
        birationalDivisorRange F
          (birationalIsotropicBaseRepresentative F baseObject).object :=
  Iff.rfl

/-- The base-indexed birational divisor ranges are stable under arbitrary
base pull-back.  The proof realizes the base arrow by a target pull-back,
then identifies its isotropic source with the chosen source representative. -/
theorem gpPullback_mem_birationalBaseDivisorRange
    {source target : F.baseCategory} (arrow : source ⟶ target)
    {divisor : Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj target).carrier}
    (membership : divisor ∈ birationalBaseDivisorRange F target) :
    F.preFrobenioid.divisorMonoid.gpPullback arrow divisor ∈
      birationalBaseDivisorRange F source := by
  let sourceRepresentative :=
    birationalIsotropicBaseRepresentative F source
  let targetRepresentative :=
    birationalIsotropicBaseRepresentative F target
  let baseArrow : F.preFrobenioid.base.obj sourceRepresentative.object ⟶
      F.preFrobenioid.base.obj targetRepresentative.object :=
    sourceRepresentative.baseIso.hom ≫ arrow ≫
      targetRepresentative.baseIso.inv
  let baseTarget : (preFrobenioid F).BaseSliceObject
      ((localizationFunctor F).obj targetRepresentative.object) :=
    { source := F.preFrobenioid.base.obj sourceRepresentative.object
      hom := baseArrow }
  obtain ⟨lifted, liftedPullback, ⟨baseComparison⟩⟩ :=
    (birational_pullbackBaseSlices F
      ((localizationFunctor F).obj targetRepresentative.object)).essentiallySurjective
      baseTarget
  have liftedProperties :=
    birational_pullback_linear_lbInvertible F lifted.hom liftedPullback
  have liftedIsotropic :
      (preFrobenioid F).IsIsotropic lifted.source :=
    birational_isIsotropic_source_of_coAngular_linear F lifted.hom
      liftedProperties.2.1 liftedProperties.1 targetRepresentative.isotropic
  obtain ⟨targetIso, targetIsoBase⟩ :=
    birational_iso_over_baseIso_of_isotropic F lifted.source
      ((localizationFunctor F).obj sourceRepresentative.object)
      liftedIsotropic sourceRepresentative.isotropic baseComparison.iso
  have representativeMembership :
      F.preFrobenioid.divisorMonoid.gpPullback
          targetRepresentative.baseIso.hom divisor ∈
        birationalDivisorRange F targetRepresentative.object :=
    (mem_birationalBaseDivisorRange_iff F target divisor).1 membership
  have liftedMembership :=
    gpPullback_mem_birationalDivisorRange_of_pullback F lifted.hom
      liftedPullback representativeMembership
  have baseComparisonPath :
      baseComparison.iso.hom ≫ baseArrow =
        (preFrobenioid F).base.map lifted.hom := by
    simpa only [baseTarget] using baseComparison.hom_commutes
  have basePath :
      (preFrobenioid F).base.map lifted.hom ≫
          targetRepresentative.baseIso.hom =
        (baseComparison.iso.hom ≫
          sourceRepresentative.baseIso.hom) ≫ arrow := by
    calc
      (preFrobenioid F).base.map lifted.hom ≫
            targetRepresentative.baseIso.hom =
          (baseComparison.iso.hom ≫ baseArrow) ≫
            targetRepresentative.baseIso.hom := by
              exact congrArg
                (fun candidate ↦ candidate ≫
                  targetRepresentative.baseIso.hom)
                baseComparisonPath.symm
      _ = (baseComparison.iso.hom ≫
            sourceRepresentative.baseIso.hom) ≫ arrow := by
          simp [baseArrow, Category.assoc]
  apply (mem_birationalBaseDivisorRange_iff F source _).2
  apply (gpPullback_mem_birationalDivisorRange_iff_of_isIso F
    targetIso.hom
    (F.preFrobenioid.divisorMonoid.gpPullback
      sourceRepresentative.baseIso.hom
      (F.preFrobenioid.divisorMonoid.gpPullback arrow divisor))).1
  have comparisonMembership :
      F.preFrobenioid.divisorMonoid.gpPullback baseComparison.iso.hom
        (F.preFrobenioid.divisorMonoid.gpPullback
          sourceRepresentative.baseIso.hom
          (F.preFrobenioid.divisorMonoid.gpPullback arrow divisor)) ∈
        birationalDivisorRange F lifted.1.1.obj := by
    convert liftedMembership using 1
    calc
      F.preFrobenioid.divisorMonoid.gpPullback baseComparison.iso.hom
            (F.preFrobenioid.divisorMonoid.gpPullback
              sourceRepresentative.baseIso.hom
              (F.preFrobenioid.divisorMonoid.gpPullback arrow divisor)) =
          F.preFrobenioid.divisorMonoid.gpPullback
            (baseComparison.iso.hom ≫
              sourceRepresentative.baseIso.hom)
            (F.preFrobenioid.divisorMonoid.gpPullback arrow divisor) :=
        (DFunLike.congr_fun
          (F.preFrobenioid.divisorMonoid.gpPullback_comp
            baseComparison.iso.hom sourceRepresentative.baseIso.hom)
          (F.preFrobenioid.divisorMonoid.gpPullback arrow divisor)).symm
      _ = F.preFrobenioid.divisorMonoid.gpPullback
            ((baseComparison.iso.hom ≫
              sourceRepresentative.baseIso.hom) ≫ arrow) divisor :=
        (DFunLike.congr_fun
          (F.preFrobenioid.divisorMonoid.gpPullback_comp
            (baseComparison.iso.hom ≫
              sourceRepresentative.baseIso.hom) arrow) divisor).symm
      _ = F.preFrobenioid.divisorMonoid.gpPullback
            ((preFrobenioid F).base.map lifted.hom ≫
              targetRepresentative.baseIso.hom) divisor := by
        exact congrArg
          (fun candidate ↦
            F.preFrobenioid.divisorMonoid.gpPullback candidate divisor)
          basePath.symm
      _ = F.preFrobenioid.divisorMonoid.gpPullback
            ((preFrobenioid F).base.map lifted.hom)
            (F.preFrobenioid.divisorMonoid.gpPullback
              targetRepresentative.baseIso.hom divisor) :=
        DFunLike.congr_fun
          (F.preFrobenioid.divisorMonoid.gpPullback_comp
            ((preFrobenioid F).base.map lifted.hom)
            targetRepresentative.baseIso.hom) divisor
  have pullbackMapsEqual := congrArg
    F.preFrobenioid.divisorMonoid.gpPullback targetIsoBase
  exact pullbackMapsEqual.symm ▸ comparisonMembership

/-- Proposition 4.4(iii)'s generic contravariant divisor subfunctor
`Phi^birat ⊆ Phi^gp`. -/
def birationalDivisorSubfunctor : BirationalDivisorSubfunctor F where
  obj := birationalBaseDivisorRange F
  pullback_mem := gpPullback_mem_birationalBaseDivisorRange F

/-- Proposition 4.4(iii)'s restricted elementary category
`F_(Phi^birat)`. -/
abbrev BirationalRestrictedElementaryFrobenioid :=
  RestrictedGroupifiedElementaryFrobenioid F
    (birationalDivisorSubfunctor F)

/-- The canonical faithful inclusion
`F_(Phi^birat) → F_(Phi^gp)`. -/
def birationalRestrictedElementaryInclusion :
    BirationalRestrictedElementaryFrobenioid F ⥤
      GroupifiedElementaryFrobenioid
        F.preFrobenioid.divisorMonoid :=
  RestrictedGroupifiedElementaryFrobenioid.inclusion F
    (birationalDivisorSubfunctor F)

theorem birationalRestrictedElementaryInclusion_faithful :
    (birationalRestrictedElementaryInclusion F).Faithful :=
  RestrictedGroupifiedElementaryFrobenioid.inclusion_faithful F
    (birationalDivisorSubfunctor F)

/-- Transport an objectwise birational divisor to the base-indexed range
along the chosen representative's base isomorphism. -/
def birationalDivisorRangeToBase (baseObject : F.baseCategory) :
    birationalDivisorRange F
        (birationalIsotropicBaseRepresentative F baseObject).object →+
      birationalBaseDivisorRange F baseObject where
  toFun divisor := by
    let representative :=
      birationalIsotropicBaseRepresentative F baseObject
    refine ⟨F.preFrobenioid.divisorMonoid.gpPullback
      representative.baseIso.inv divisor.1, ?_⟩
    apply (mem_birationalBaseDivisorRange_iff F baseObject _).2
    have pullbackComposition :=
      F.preFrobenioid.divisorMonoid.gpPullback_comp
        representative.baseIso.hom representative.baseIso.inv
    change F.preFrobenioid.divisorMonoid.gpPullback
        representative.baseIso.hom
        (F.preFrobenioid.divisorMonoid.gpPullback
          representative.baseIso.inv divisor.1) ∈
      birationalDivisorRange F representative.object
    rw [← AddMonoidHom.comp_apply, ← pullbackComposition,
      representative.baseIso.hom_inv_id,
      F.preFrobenioid.divisorMonoid.gpPullback_id,
      AddMonoidHom.id_apply]
    exact divisor.property
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' left right := by
    apply Subtype.ext
    exact map_add _ left.1 right.1

/-- The rational-function divisor homomorphism with codomain restricted to
its literal objectwise image. -/
def birationalRationalFunctionDivisorRangeHom
    (object : F.carrier) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism
        ((localizationFunctor F).obj object) →*
      Multiplicative (birationalDivisorRange F object) where
  toFun value := Multiplicative.ofAdd
    ⟨((groupifiedBirationalFunctor F).map value.hom).divisor,
      (mem_birationalDivisorRange_iff F object _).2 ⟨value, rfl⟩⟩
  map_one' := by
    apply Multiplicative.ext
    apply Subtype.ext
    change ((groupifiedBirationalFunctor F).map (𝟙 _)).divisor = 0
    rw [(groupifiedBirationalFunctor F).map_id]
    rfl
  map_mul' left right := by
    apply Multiplicative.ext
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((birationalRationalFunctionDivisorHom F object).map_mul left right)

/-- Proposition 4.4(iii)'s base-indexed rational-function divisor map, using
the chosen isotropic representative over the base object. -/
def birationalBaseDivisorHom (baseObject : F.baseCategory) :
    (preFrobenioid F).LinearBaseIdentityEndomorphism
        ((localizationFunctor F).obj
          (birationalIsotropicBaseRepresentative F baseObject).object) →*
      Multiplicative (birationalBaseDivisorRange F baseObject) :=
  (birationalDivisorRangeToBase F baseObject).toMultiplicative.comp
    (birationalRationalFunctionDivisorRangeHom F
      (birationalIsotropicBaseRepresentative F baseObject).object)

/-- The base-indexed rational-function divisor map is objectwise
surjective. -/
theorem birationalBaseDivisorHom_surjective
    (baseObject : F.baseCategory) :
    Function.Surjective (birationalBaseDivisorHom F baseObject) := by
  intro divisor
  let representative :=
    birationalIsotropicBaseRepresentative F baseObject
  have representativeMembership :
      F.preFrobenioid.divisorMonoid.gpPullback
          representative.baseIso.hom divisor.toAdd.1 ∈
        birationalDivisorRange F representative.object :=
    (mem_birationalBaseDivisorRange_iff F baseObject divisor.toAdd.1).1
      divisor.toAdd.property
  obtain ⟨value, valueDivisor⟩ :=
    (mem_birationalDivisorRange_iff F representative.object _).1
      representativeMembership
  refine ⟨value, ?_⟩
  apply Multiplicative.ext
  apply Subtype.ext
  change F.preFrobenioid.divisorMonoid.gpPullback
      representative.baseIso.inv
      ((groupifiedBirationalFunctor F).map value.hom).divisor =
    divisor.toAdd.1
  rw [valueDivisor]
  have pullbackComposition :=
    F.preFrobenioid.divisorMonoid.gpPullback_comp
      representative.baseIso.inv representative.baseIso.hom
  rw [← AddMonoidHom.comp_apply, ← pullbackComposition,
    representative.baseIso.inv_hom_id,
    F.preFrobenioid.divisorMonoid.gpPullback_id,
    AddMonoidHom.id_apply]

/-- The base-indexed divisor map has exactly the localized source units as
its kernel. -/
theorem birationalBaseDivisorHom_eq_one_iff_sourceUnitImage
    (baseObject : F.baseCategory)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism
      ((localizationFunctor F).obj
        (birationalIsotropicBaseRepresentative F baseObject).object)) :
    birationalBaseDivisorHom F baseObject value = 1 ↔
      ∃ unit : F.preFrobenioid.BaseIdentityAutomorphism
          (birationalIsotropicBaseRepresentative F baseObject).object,
        localizationUnitEndomorphism F
          (birationalIsotropicBaseRepresentative F baseObject).object unit =
            value := by
  let representative :=
    birationalIsotropicBaseRepresentative F baseObject
  have baseEquality :
      birationalBaseDivisorHom F baseObject value = 1 ↔
        F.preFrobenioid.divisorMonoid.gpPullback
          representative.baseIso.inv
          ((groupifiedBirationalFunctor F).map value.hom).divisor = 0 := by
    constructor
    · intro equality
      exact congrArg
        (fun result : Multiplicative
            (birationalBaseDivisorRange F baseObject) ↦
          result.toAdd.1) equality
    · intro equality
      apply Multiplicative.ext
      apply Subtype.ext
      exact equality
  rw [baseEquality]
  have pullbackInjective : Function.Injective
      (F.preFrobenioid.divisorMonoid.gpPullback
        representative.baseIso.inv) := by
    intro left right equality
    have mapped := congrArg
      (F.preFrobenioid.divisorMonoid.gpPullback
        representative.baseIso.hom) equality
    have pullbackComposition :=
      F.preFrobenioid.divisorMonoid.gpPullback_comp
        representative.baseIso.hom representative.baseIso.inv
    simpa only [← AddMonoidHom.comp_apply, ← pullbackComposition,
      representative.baseIso.hom_inv_id,
      F.preFrobenioid.divisorMonoid.gpPullback_id,
      AddMonoidHom.id_apply] using mapped
  rw [← map_zero
    (F.preFrobenioid.divisorMonoid.gpPullback representative.baseIso.inv),
    pullbackInjective.eq_iff]
  exact birational_groupifiedDivisor_eq_zero_iff_sourceUnitImage F
    representative.object value

/-- A candidate subgroup family is the birational rational-divisor image
when its values are exactly detected on the chosen isotropic
representatives. -/
structure IsBirationalDivisorImage
    (candidate : BirationalDivisorSubfunctor F) : Prop where
  mem_iff : ∀ (baseObject : F.baseCategory)
    (divisor : Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj baseObject).carrier),
    divisor ∈ candidate.obj baseObject ↔
      F.preFrobenioid.divisorMonoid.gpPullback
          (birationalIsotropicBaseRepresentative F baseObject).baseIso.hom
          divisor ∈
        birationalDivisorRange F
          (birationalIsotropicBaseRepresentative F baseObject).object

/-- The constructed `Phi^birat` has the rational-image characterization. -/
theorem birationalDivisorSubfunctor_isBirationalDivisorImage :
    IsBirationalDivisorImage F (birationalDivisorSubfunctor F) :=
  ⟨mem_birationalBaseDivisorRange_iff F⟩

/-- Proposition 4.4(iii)'s uniqueness clause at the rational-image layer. -/
theorem birationalDivisorSubfunctor_unique
    (candidate : BirationalDivisorSubfunctor F)
    (candidateImage : IsBirationalDivisorImage F candidate) :
    candidate = birationalDivisorSubfunctor F := by
  apply BirationalDivisorSubfunctor.ext
  funext baseObject
  ext divisor
  exact (candidateImage.mem_iff baseObject divisor).trans
    (mem_birationalBaseDivisorRange_iff F baseObject divisor).symm

end

end Iut.FrobenioidBirationalization
