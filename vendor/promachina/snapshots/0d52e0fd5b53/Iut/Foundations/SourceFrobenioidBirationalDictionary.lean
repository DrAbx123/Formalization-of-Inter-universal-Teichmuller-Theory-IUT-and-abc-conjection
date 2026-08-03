/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidBirationalization

/-!
# The structural dictionary for arbitrary Frobenioid birationalization

This file begins the presentation-independent morphism dictionary in
Frobenioids I, Proposition 4.4(iv).  The localization functor preserves the
base arrow and Frobenius degree because its structure functor is the unique
extension of the source structure functor after forgetting the divisor.  Its
target divisor lies in the terminal monoid, so every localized arrow is an
isometry.

The results here use only an arbitrary `FrobenioidPresentation`; no
Theorem 5.2 coordinates or model-specific rational-function formulas occur.
-/

open CategoryTheory

namespace Iut.FrobenioidBirationalization

universe u

noncomputable section

variable (F : FrobenioidPresentation.{u})

/-- Proposition 4.4(iv): the canonical localization preserves the base
arrow. -/
theorem localization_map_base
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).base.map ((localizationFunctor F).map arrow) =
      F.preFrobenioid.base.map arrow := by
  simp only [preFrobenioid, PreFrobenioid.base, structureFunctor,
    localizationFunctor, forgetDivisorFunctor,
    Localization.Construction.lift]
  dsimp [MorphismProperty.Q, CategoryTheory.Quotient.lift,
    Quot.liftOn, Quotient.functor]
  rw [CategoryTheory.composePath_toPath]
  rfl

/-- Proposition 4.4(iv): the canonical localization preserves Frobenius
degree. -/
theorem localization_map_frobeniusDegree
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).frobeniusDegree
      ((localizationFunctor F).map arrow) =
      F.preFrobenioid.frobeniusDegree arrow := by
  simp only [preFrobenioid, PreFrobenioid.frobeniusDegree,
    structureFunctor, localizationFunctor, forgetDivisorFunctor,
    Localization.Construction.lift]
  dsimp [MorphismProperty.Q, CategoryTheory.Quotient.lift,
    Quot.liftOn, Quotient.functor]
  rw [CategoryTheory.composePath_toPath]

/-- The degree statement in Proposition 4.4(iv), at an arbitrary fixed
positive degree. -/
theorem localization_map_frobeniusDegree_eq_iff
    {source target : F.carrier} (arrow : source ⟶ target)
    (degree : ℕ+) :
    (preFrobenioid F).frobeniusDegree
        ((localizationFunctor F).map arrow) = degree ↔
      F.preFrobenioid.frobeniusDegree arrow = degree := by
  rw [localization_map_frobeniusDegree F arrow]

/-- Proposition 4.4(iv): the canonical localization preserves and reflects
the base-isomorphism predicate. -/
theorem localization_map_isBaseIso_iff
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).IsBaseIso ((localizationFunctor F).map arrow) ↔
      F.preFrobenioid.IsBaseIso arrow := by
  change IsIso
      ((preFrobenioid F).base.map ((localizationFunctor F).map arrow)) ↔
    IsIso (F.preFrobenioid.base.map arrow)
  rw [localization_map_base F arrow]
  exact Iff.rfl

/-- Proposition 4.4(iv): the canonical localization preserves and reflects
linearity. -/
theorem localization_map_isLinear_iff
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).IsLinear ((localizationFunctor F).map arrow) ↔
      F.preFrobenioid.IsLinear arrow := by
  change (preFrobenioid F).frobeniusDegree
      ((localizationFunctor F).map arrow) = 1 ↔
    F.preFrobenioid.frobeniusDegree arrow = 1
  rw [localization_map_frobeniusDegree F arrow]

/-- Proposition 4.4(iv): the canonical localization preserves and reflects
pre-steps. -/
theorem localization_map_isPreStep_iff
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).IsPreStep ((localizationFunctor F).map arrow) ↔
      F.preFrobenioid.IsPreStep arrow := by
  rw [PreFrobenioid.IsPreStep, PreFrobenioid.IsPreStep,
    localization_map_isLinear_iff F arrow,
    localization_map_isBaseIso_iff F arrow]

/-- Cancelling a generic roof denominator recovers its numerator. -/
@[reassoc]
theorem localization_map_denominator_comp_roofValue
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (localizationFunctor F).map denominator.hom ≫
        CoAngularPreStepOver.roofValue F denominator numerator =
      (localizationFunctor F).map numerator := by
  exact MorphismProperty.RightFraction.map_s_comp_map
    (MorphismProperty.RightFraction.mk denominator.hom
      denominator.property numerator)
    (localizationFunctor F) (MorphismProperty.Q_inverts (denominators F))

/-- Postcomposing a roof by a localized source arrow postcomposes its
numerator. -/
@[reassoc]
theorem roofValue_comp_localization_map
    {source middle target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ middle)
    (arrow : middle ⟶ target) :
    CoAngularPreStepOver.roofValue F denominator numerator ≫
        (localizationFunctor F).map arrow =
      CoAngularPreStepOver.roofValue F denominator
        (numerator ≫ arrow) := by
  unfold CoAngularPreStepOver.roofValue
  dsimp only [MorphismProperty.RightFraction.map]
  rw [Category.assoc, ← (localizationFunctor F).map_comp]

/-- Precomposing a roof by a localized source arrow is computed by any
right-Ore square between that arrow and the roof denominator. -/
theorem localization_map_comp_roofValue
    {source middle target : F.carrier}
    (arrow : source ⟶ middle)
    (denominator : CoAngularPreStepOver F middle)
    (numerator : denominator.source ⟶ target)
    (square : RightOreSquare F denominator.hom arrow) :
    (localizationFunctor F).map arrow ≫
        CoAngularPreStepOver.roofValue F denominator numerator =
      CoAngularPreStepOver.roofValue F
        { source := square.source
          hom := square.refinement
          property := square.refinement_property }
        (square.across ≫ numerator) := by
  let localization := localizationFunctor F
  let refinedDenominator : CoAngularPreStepOver F source :=
    { source := square.source
      hom := square.refinement
      property := square.refinement_property }
  have mappedRefinementIso : IsIso (localization.map square.refinement) :=
    MorphismProperty.Q_inverts (denominators F) square.refinement
      square.refinement_property
  letI : IsIso (localization.map square.refinement) :=
    mappedRefinementIso
  apply (cancel_epi (localization.map square.refinement)).1
  calc
    localization.map square.refinement ≫
          (localization.map arrow ≫
            CoAngularPreStepOver.roofValue F denominator numerator) =
        localization.map (square.refinement ≫ arrow) ≫
          CoAngularPreStepOver.roofValue F denominator numerator := by
      rw [← Category.assoc, localization.map_comp]
    _ = localization.map (square.across ≫ denominator.hom) ≫
          CoAngularPreStepOver.roofValue F denominator numerator := by
      rw [square.commutes]
    _ = (localization.map square.across ≫
          localization.map denominator.hom) ≫
          CoAngularPreStepOver.roofValue F denominator numerator := by
      rw [localization.map_comp]
    _ = localization.map square.across ≫
          localization.map numerator := by
      rw [Category.assoc,
        localization_map_denominator_comp_roofValue]
    _ = localization.map (square.across ≫ numerator) := by
      rw [localization.map_comp]
    _ = localization.map square.refinement ≫
          CoAngularPreStepOver.roofValue F refinedDenominator
            (square.across ≫ numerator) := by
      simpa [localization] using
        (localization_map_denominator_comp_roofValue F refinedDenominator
          (square.across ≫ numerator)).symm

/-- For a fixed denominator, roof evaluation is injective in its numerator.
Cancel the inverted denominator and use faithfulness of localization. -/
theorem roofValue_injective
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source) :
    Function.Injective
      (CoAngularPreStepOver.roofValue F denominator
        (target := target)) := by
  intro first second equality
  apply (localizationFunctor_faithful F).map_injective
  have cancelled := congrArg
    (fun value ↦
      (localizationFunctor F).map denominator.hom ≫ value)
    equality
  simpa only [localization_map_denominator_comp_roofValue] using cancelled

/-- Every source arrow remains epic in the birational localization.  Two
postcomposed roofs are first refined to one common denominator; a second Ore
square computes their precomposition by the source arrow.  Fixed-denominator
injectivity and source total epimorphicity then cancel the remaining source
refinement. -/
theorem localization_map_epi
    {source target : F.carrier} (arrow : source ⟶ target) :
    Epi ((localizationFunctor F).map arrow) := by
  constructor
  intro testObject first second compositeEquality
  obtain ⟨test, rfl⟩ :=
    (Localization.Construction.objEquiv (denominators F)).surjective
      testObject
  let localization := localizationFunctor F
  letI := hasRightCalculusOfFractions F
  obtain ⟨firstFraction, firstRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localization) (W := denominators F) first
  obtain ⟨secondFraction, secondRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localization) (W := denominators F) second
  let firstDenominator : CoAngularPreStepOver F target :=
    { source := firstFraction.X'
      hom := firstFraction.s
      property := firstFraction.hs }
  let secondDenominator : CoAngularPreStepOver F target :=
    { source := secondFraction.X'
      hom := secondFraction.s
      property := secondFraction.hs }
  have firstRoof :
      CoAngularPreStepOver.roofValue F firstDenominator firstFraction.f =
        first := by
    change firstFraction.map localization
      (MorphismProperty.Q_inverts (denominators F)) = first
    exact firstRepresents.symm
  have secondRoof :
      CoAngularPreStepOver.roofValue F secondDenominator
          secondFraction.f = second := by
    change secondFraction.map localization
      (MorphismProperty.Q_inverts (denominators F)) = second
    exact secondRepresents.symm
  let commonSquare := rightOreSquare F firstFraction.s secondFraction.s
    firstFraction.hs
  have commonProperty : denominators F
      (commonSquare.refinement ≫ secondFraction.s) :=
    denominators_comp F commonSquare.refinement secondFraction.s
      commonSquare.refinement_property secondFraction.hs
  let commonDenominator : CoAngularPreStepOver F target :=
    { source := commonSquare.source
      hom := commonSquare.refinement ≫ secondFraction.s
      property := commonProperty }
  let toFirst : commonDenominator ⟶ firstDenominator :=
    { hom := commonSquare.across
      commutes := by
        change commonSquare.across ≫ firstFraction.s =
          commonSquare.refinement ≫ secondFraction.s
        exact commonSquare.commutes.symm }
  let toSecond : commonDenominator ⟶ secondDenominator :=
    { hom := commonSquare.refinement
      commutes := rfl }
  have firstCommon :
      CoAngularPreStepOver.roofValue F commonDenominator
          (commonSquare.across ≫ firstFraction.f) = first :=
    (CoAngularPreStepOver.roofValue_transition F toFirst
      firstFraction.f).trans firstRoof
  have secondCommon :
      CoAngularPreStepOver.roofValue F commonDenominator
          (commonSquare.refinement ≫ secondFraction.f) = second :=
    (CoAngularPreStepOver.roofValue_transition F toSecond
      secondFraction.f).trans secondRoof
  have commonCompositeEquality :
      localization.map arrow ≫
          CoAngularPreStepOver.roofValue F commonDenominator
            (commonSquare.across ≫ firstFraction.f) =
        localization.map arrow ≫
          CoAngularPreStepOver.roofValue F commonDenominator
            (commonSquare.refinement ≫ secondFraction.f) := by
    rw [firstCommon, secondCommon]
    exact compositeEquality
  let precompositionSquare := rightOreSquare F commonDenominator.hom
    arrow commonDenominator.property
  have refinedRoofEquality :
      CoAngularPreStepOver.roofValue F
          { source := precompositionSquare.source
            hom := precompositionSquare.refinement
            property := precompositionSquare.refinement_property }
          (precompositionSquare.across ≫ commonSquare.across ≫
            firstFraction.f) =
        CoAngularPreStepOver.roofValue F
          { source := precompositionSquare.source
            hom := precompositionSquare.refinement
            property := precompositionSquare.refinement_property }
          (precompositionSquare.across ≫ commonSquare.refinement ≫
            secondFraction.f) := by
    rw [localization_map_comp_roofValue F arrow commonDenominator
      (commonSquare.across ≫ firstFraction.f) precompositionSquare,
      localization_map_comp_roofValue F arrow commonDenominator
        (commonSquare.refinement ≫ secondFraction.f)
        precompositionSquare] at commonCompositeEquality
    simpa only [Category.assoc] using commonCompositeEquality
  have refinedNumeratorEquality :
      precompositionSquare.across ≫ commonSquare.across ≫
          firstFraction.f =
        precompositionSquare.across ≫ commonSquare.refinement ≫
          secondFraction.f :=
    roofValue_injective F
      ({ source := precompositionSquare.source
         hom := precompositionSquare.refinement
         property := precompositionSquare.refinement_property } :
        CoAngularPreStepOver F source) refinedRoofEquality
  haveI : Epi precompositionSquare.across :=
    F.carrierTotallyEpimorphic precompositionSquare.across
  have commonNumeratorEquality :
      commonSquare.across ≫ firstFraction.f =
        commonSquare.refinement ≫ secondFraction.f := by
    apply (cancel_epi precompositionSquare.across).1
    simpa only [Category.assoc] using refinedNumeratorEquality
  rw [← firstCommon, ← secondCommon, commonNumeratorEquality]

/-- A source monomorphism remains monic in the generic right-fraction
localization.  Equality after its image gives a relation between the two
composite roofs; cancelling the source monomorphism in that relation gives a
relation between the original roofs. -/
theorem localization_map_mono_of_mono
    {source target : F.carrier} (arrow : source ⟶ target)
    (arrowMono : Mono arrow) :
    Mono ((localizationFunctor F).map arrow) := by
  letI : Mono arrow := arrowMono
  constructor
  intro testObject first second compositeEquality
  obtain ⟨test, rfl⟩ :=
    (Localization.Construction.objEquiv (denominators F)).surjective
      testObject
  let localization := localizationFunctor F
  letI := hasRightCalculusOfFractions F
  obtain ⟨firstFraction, firstRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localization) (W := denominators F) first
  obtain ⟨secondFraction, secondRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localization) (W := denominators F) second
  let firstDenominator : CoAngularPreStepOver F test :=
    { source := firstFraction.X'
      hom := firstFraction.s
      property := firstFraction.hs }
  let secondDenominator : CoAngularPreStepOver F test :=
    { source := secondFraction.X'
      hom := secondFraction.s
      property := secondFraction.hs }
  have firstRoof :
      CoAngularPreStepOver.roofValue F firstDenominator firstFraction.f =
        first := by
    change firstFraction.map localization
      (MorphismProperty.Q_inverts (denominators F)) = first
    exact firstRepresents.symm
  have secondRoof :
      CoAngularPreStepOver.roofValue F secondDenominator
          secondFraction.f = second := by
    change secondFraction.map localization
      (MorphismProperty.Q_inverts (denominators F)) = second
    exact secondRepresents.symm
  have roofCompositeEquality :
      CoAngularPreStepOver.roofValue F firstDenominator
          (firstFraction.f ≫ arrow) =
        CoAngularPreStepOver.roofValue F secondDenominator
          (secondFraction.f ≫ arrow) := by
    rw [← roofValue_comp_localization_map,
      ← roofValue_comp_localization_map, firstRoof, secondRoof]
    exact compositeEquality
  unfold CoAngularPreStepOver.roofValue at roofCompositeEquality
  have fractionRelation :=
    (MorphismProperty.RightFraction.map_eq_iff
      (L := localization) (W := denominators F) _ _).1
      roofCompositeEquality
  rcases fractionRelation with
    ⟨commonSource, toFirst, toSecond, denominatorEquality,
      numeratorCompositeEquality, commonProperty⟩
  have refinedNumeratorEquality :
      toFirst ≫ firstFraction.f = toSecond ≫ secondFraction.f := by
    apply (cancel_mono arrow).1
    simpa only [Category.assoc] using numeratorCompositeEquality
  have originalFractionRelation :
      MorphismProperty.RightFractionRel firstFraction secondFraction :=
    ⟨commonSource, toFirst, toSecond, denominatorEquality,
      refinedNumeratorEquality, commonProperty⟩
  have mappedFractionEquality :
      firstFraction.map localization
          (MorphismProperty.Q_inverts (denominators F)) =
        secondFraction.map localization
          (MorphismProperty.Q_inverts (denominators F)) :=
    (MorphismProperty.RightFraction.map_eq_iff
      (L := localization) (W := denominators F) _ _).2
      originalFractionRelation
  exact firstRepresents.trans
    (mappedFractionEquality.trans secondRepresents.symm)

/-- Applying the birational base functor to a roof cancellation gives the
base-arrow formula used throughout Proposition 4.4(iv). -/
theorem denominator_base_comp_roofValue_base
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    F.preFrobenioid.base.map denominator.hom ≫
        (preFrobenioid F).base.map
          (CoAngularPreStepOver.roofValue F denominator numerator) =
      F.preFrobenioid.base.map numerator := by
  have equality := congrArg
    (fun arrow ↦ (preFrobenioid F).base.map arrow)
    (localization_map_denominator_comp_roofValue F denominator numerator)
  dsimp only at equality
  rw [(preFrobenioid F).base.map_comp,
    localization_map_base F denominator.hom,
    localization_map_base F numerator] at equality
  exact equality

/-- A roof has the Frobenius degree of its numerator: every denominator is
a degree-one pre-step. -/
theorem roofValue_frobeniusDegree
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (preFrobenioid F).frobeniusDegree
        (CoAngularPreStepOver.roofValue F denominator numerator) =
      F.preFrobenioid.frobeniusDegree numerator := by
  have equality := congrArg (preFrobenioid F).frobeniusDegree
    (localization_map_denominator_comp_roofValue F denominator numerator)
  rw [(preFrobenioid F).frobeniusDegree_comp,
    localization_map_frobeniusDegree F denominator.hom,
    localization_map_frobeniusDegree F numerator,
    denominator.property.1.1] at equality
  simpa using equality

/-- A localized roof is linear exactly when its numerator is linear. -/
theorem roofValue_isLinear_iff
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (preFrobenioid F).IsLinear
        (CoAngularPreStepOver.roofValue F denominator numerator) ↔
      F.preFrobenioid.IsLinear numerator := by
  change (preFrobenioid F).frobeniusDegree
      (CoAngularPreStepOver.roofValue F denominator numerator) = 1 ↔
    F.preFrobenioid.frobeniusDegree numerator = 1
  rw [roofValue_frobeniusDegree F denominator numerator]

/-- A localized roof is a base isomorphism exactly when its numerator is:
the denominator already has invertible base. -/
theorem roofValue_isBaseIso_iff
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (preFrobenioid F).IsBaseIso
        (CoAngularPreStepOver.roofValue F denominator numerator) ↔
      F.preFrobenioid.IsBaseIso numerator := by
  have baseEquation :
      F.preFrobenioid.base.map denominator.hom ≫
          (preFrobenioid F).base.map
            (CoAngularPreStepOver.roofValue F denominator numerator) =
        F.preFrobenioid.base.map numerator :=
    denominator_base_comp_roofValue_base F denominator numerator
  constructor
  · intro roofIsIso
    let denominatorBaseIsIso :
        IsIso (F.preFrobenioid.base.map denominator.hom) :=
      denominator.property.1.2
    change IsIso ((preFrobenioid F).base.map
      (CoAngularPreStepOver.roofValue F denominator numerator)) at roofIsIso
    letI roofBaseIsIso : IsIso ((preFrobenioid F).base.map
        (CoAngularPreStepOver.roofValue F denominator numerator)) :=
      roofIsIso
    change IsIso (F.preFrobenioid.base.map numerator)
    rw [← baseEquation]
    exact IsIso.comp_isIso' denominatorBaseIsIso roofBaseIsIso
  · intro numeratorIsIso
    letI denominatorBaseIsIso :
        IsIso (F.preFrobenioid.base.map denominator.hom) :=
      denominator.property.1.2
    change IsIso (F.preFrobenioid.base.map numerator) at numeratorIsIso
    letI numeratorBaseIsIso : IsIso (F.preFrobenioid.base.map numerator) :=
      numeratorIsIso
    change IsIso ((preFrobenioid F).base.map
      (CoAngularPreStepOver.roofValue F denominator numerator))
    exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
      denominatorBaseIsIso numeratorBaseIsIso baseEquation

/-- A localized roof is a pre-step exactly when its numerator is a source
pre-step. -/
theorem roofValue_isPreStep_iff
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (preFrobenioid F).IsPreStep
        (CoAngularPreStepOver.roofValue F denominator numerator) ↔
      F.preFrobenioid.IsPreStep numerator := by
  rw [PreFrobenioid.IsPreStep, PreFrobenioid.IsPreStep,
    roofValue_isLinear_iff F denominator numerator,
    roofValue_isBaseIso_iff F denominator numerator]

/-- The exact source roof data classifying a base-identity endomorphism in
Proposition 4.4(iv). -/
structure BaseIdentityRoof
    (object : F.carrier)
    (arrow : (localizationFunctor F).obj object ⟶
      (localizationFunctor F).obj object) where
  denominator : CoAngularPreStepOver F object
  numerator : denominator.source ⟶ object
  baseEquivalent :
    F.preFrobenioid.base.map numerator =
      F.preFrobenioid.base.map denominator.hom
  represents :
    CoAngularPreStepOver.roofValue F denominator numerator = arrow

/-- A base-identity localized endomorphism has a representative whose
numerator and denominator induce the same base arrow. -/
theorem baseIdentityRoof_of_isBaseIdentity
    {object : F.carrier}
    (arrow : (localizationFunctor F).obj object ⟶
      (localizationFunctor F).obj object)
    (baseIdentity : (preFrobenioid F).IsBaseIdentity arrow) :
    Nonempty (BaseIdentityRoof F object arrow) := by
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F object :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofBaseIdentity :
      (preFrobenioid F).base.map
          (CoAngularPreStepOver.roofValue F denominator fraction.f) =
        𝟙 (F.preFrobenioid.base.obj object) := by
    rw [represents] at baseIdentity
    simpa only [CoAngularPreStepOver.roofValue, denominator] using
      baseIdentity
  have baseEquivalent :
      F.preFrobenioid.base.map fraction.f =
        F.preFrobenioid.base.map denominator.hom := by
    have cancellation := denominator_base_comp_roofValue_base F
      denominator fraction.f
    rw [roofBaseIdentity] at cancellation
    calc
      F.preFrobenioid.base.map fraction.f =
          F.preFrobenioid.base.map denominator.hom ≫
            𝟙 (F.preFrobenioid.base.obj object) := cancellation.symm
      _ = F.preFrobenioid.base.map denominator.hom :=
        Category.comp_id _
  exact ⟨
    { denominator := denominator
      numerator := fraction.f
      baseEquivalent := baseEquivalent
      represents := represents.symm }⟩

/-- A roof whose numerator and denominator have the same base arrow is a
base-identity endomorphism. -/
theorem isBaseIdentity_of_baseIdentityRoof
    {object : F.carrier}
    {arrow : (localizationFunctor F).obj object ⟶
      (localizationFunctor F).obj object}
    (roof : BaseIdentityRoof F object arrow) :
    (preFrobenioid F).IsBaseIdentity arrow := by
  haveI : IsIso (F.preFrobenioid.base.map roof.denominator.hom) :=
    roof.denominator.property.1.2
  change (preFrobenioid F).base.map arrow =
    𝟙 (F.preFrobenioid.base.obj object)
  rw [← roof.represents]
  apply (cancel_epi (F.preFrobenioid.base.map roof.denominator.hom)).1
  calc
    F.preFrobenioid.base.map roof.denominator.hom ≫
        (preFrobenioid F).base.map
          (CoAngularPreStepOver.roofValue F roof.denominator roof.numerator) =
      F.preFrobenioid.base.map roof.numerator :=
        denominator_base_comp_roofValue_base F roof.denominator roof.numerator
    _ = F.preFrobenioid.base.map roof.denominator.hom :=
      roof.baseEquivalent
    _ = F.preFrobenioid.base.map roof.denominator.hom ≫
        𝟙 (F.preFrobenioid.base.obj object) :=
      (Category.comp_id _).symm

/-- Proposition 4.4(iv): base-identity target endomorphisms are exactly the
roofs whose numerator and denominator have equal base arrows. -/
theorem isBaseIdentity_iff_nonempty_baseIdentityRoof
    {object : F.carrier}
    (arrow : (localizationFunctor F).obj object ⟶
      (localizationFunctor F).obj object) :
    (preFrobenioid F).IsBaseIdentity arrow ↔
      Nonempty (BaseIdentityRoof F object arrow) :=
  ⟨baseIdentityRoof_of_isBaseIdentity F arrow,
    fun ⟨roof⟩ ↦ isBaseIdentity_of_baseIdentityRoof F roof⟩

/-- Proposition 1.7(v), for the right factor of a co-angular pre-step.
The pre-step condition first forces the left factor to have invertible base;
the defining co-angular test may then absorb that left factor into its first
test arrow. -/
theorem isCoAngular_right_of_comp_preSteps
    {source middle target : F.carrier}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (compositePreStep : F.preFrobenioid.IsPreStep (first ≫ second))
    (compositeCoAngular : F.preFrobenioid.IsCoAngular (first ≫ second))
    (secondPreStep : F.preFrobenioid.IsPreStep second) :
    F.preFrobenioid.IsCoAngular second := by
  have firstPreStep := isPreStep_left_of_comp F first second
    compositePreStep secondPreStep
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  apply compositeCoAngular (first ≫ gamma) beta alpha
  · simpa only [Category.assoc] using
      congrArg (fun arrow ↦ first ≫ arrow) equality
  · exact alphaLinear
  · exact betaPreStep
  · exact betaIsometric
  · rcases baseAlternative with alphaBaseIso | gammaBaseIso
    · exact Or.inl alphaBaseIso
    · right
      change IsIso (F.preFrobenioid.base.map (first ≫ gamma))
      rw [F.preFrobenioid.base.map_comp]
      haveI : IsIso (F.preFrobenioid.base.map first) := firstPreStep.2
      haveI : IsIso (F.preFrobenioid.base.map gamma) := gammaBaseIso
      infer_instance

/-- Proposition 1.7(v): a pre-step right factor of a co-angular-pre-step
composite is again a co-angular pre-step. -/
theorem denominators_right_of_comp
    {source middle target : F.carrier}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (composite : denominators F (first ≫ second))
    (secondPreStep : F.preFrobenioid.IsPreStep second) :
    denominators F second :=
  ⟨secondPreStep,
    isCoAngular_right_of_comp_preSteps F first second composite.1
      composite.2 secondPreStep⟩

/-- Every isomorphism in the birational target has degree one and invertible
base, hence is a pre-step. -/
theorem birational_isPreStep_of_isIso
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (arrowIsIso : IsIso arrow) :
    (preFrobenioid F).IsPreStep arrow := by
  letI : IsIso arrow := arrowIsIso
  constructor
  · rw [PreFrobenioid.IsLinear]
    have degreeEquation := (preFrobenioid F).frobeniusDegree_comp
      arrow (inv arrow)
    rw [IsIso.hom_inv_id,
      (preFrobenioid F).frobeniusDegree_id] at degreeEquation
    apply Subtype.ext
    have valueEquation := congrArg Subtype.val degreeEquation
    change 1 =
      ((preFrobenioid F).frobeniusDegree arrow).1 *
        ((preFrobenioid F).frobeniusDegree (inv arrow)).1 at valueEquation
    exact (mul_eq_one.mp valueEquation.symm).1
  · change IsIso ((preFrobenioid F).base.map arrow)
    infer_instance

/-- Pre-steps in the birational pre-Frobenioid are closed under
composition. -/
theorem birational_isPreStep_comp
    {source middle target : BirationalCategory F}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstPreStep : (preFrobenioid F).IsPreStep first)
    (secondPreStep : (preFrobenioid F).IsPreStep second) :
    (preFrobenioid F).IsPreStep (first ≫ second) := by
  constructor
  · rw [PreFrobenioid.IsLinear,
      (preFrobenioid F).frobeniusDegree_comp,
      firstPreStep.1, secondPreStep.1]
    rfl
  · change IsIso ((preFrobenioid F).base.map (first ≫ second))
    rw [(preFrobenioid F).base.map_comp]
    haveI : IsIso ((preFrobenioid F).base.map first) := firstPreStep.2
    haveI : IsIso ((preFrobenioid F).base.map second) := secondPreStep.2
    infer_instance

/-- Two generic birational pullback-comparison targets agree on their two
data fields. -/
theorem pullbackComparisonTarget_ext
    {source target test : BirationalCategory F}
    {arrow : source ⟶ target}
    {left right :
      (preFrobenioid F).PullbackComparisonTarget arrow test}
    (toCodomain : left.toCodomain = right.toCodomain)
    (toBaseDomain : left.toBaseDomain = right.toBaseDomain) :
    left = right := by
  cases left
  cases right
  cases toCodomain
  cases toBaseDomain
  rfl

/-- Two source pullback-comparison targets agree on their two data fields. -/
theorem sourcePullbackComparisonTarget_ext
    {source target test : F.carrier}
    {arrow : source ⟶ target}
    {left right : F.preFrobenioid.PullbackComparisonTarget arrow test}
    (toCodomain : left.toCodomain = right.toCodomain)
    (toBaseDomain : left.toBaseDomain = right.toBaseDomain) :
    left = right := by
  cases left
  cases right
  cases toCodomain
  cases toBaseDomain
  rfl

/-- Precomposing a birational pullback by an isomorphism preserves the
pullback universal property. -/
theorem birational_isPullback_comp_of_isIso_left
    {source middle target : BirationalCategory F}
    (first : source ⟶ middle) (second : middle ⟶ target)
    [IsIso first]
    (secondPullback : (preFrobenioid F).IsPullback second) :
    (preFrobenioid F).IsPullback (first ≫ second) := by
  intro test
  constructor
  · intro left right equality
    have codomainEquality :
        left ≫ (first ≫ second) =
          right ≫ (first ≫ second) :=
      congrArg (fun value ↦ value.toCodomain) equality
    have baseEquality :
        (preFrobenioid F).base.map left =
          (preFrobenioid F).base.map right :=
      congrArg (fun value ↦ value.toBaseDomain) equality
    have throughFirst : left ≫ first = right ≫ first := by
      apply (secondPullback test).1
      apply pullbackComparisonTarget_ext F
      · change (left ≫ first) ≫ second =
          (right ≫ first) ≫ second
        simpa only [Category.assoc] using codomainEquality
      · change (preFrobenioid F).base.map (left ≫ first) =
          (preFrobenioid F).base.map (right ≫ first)
        rw [(preFrobenioid F).base.map_comp,
          (preFrobenioid F).base.map_comp, baseEquality]
    exact (cancel_mono first).1 throughFirst
  · intro targetComparison
    let secondComparison :
        (preFrobenioid F).PullbackComparisonTarget second test :=
      { toCodomain := targetComparison.toCodomain
        toBaseDomain := targetComparison.toBaseDomain ≫
          (preFrobenioid F).base.map first
        commutes := by
          simpa only [(preFrobenioid F).base.map_comp,
            Category.assoc] using targetComparison.commutes }
    obtain ⟨lift, liftComparison⟩ :=
      (secondPullback test).2 secondComparison
    refine ⟨lift ≫ inv first, ?_⟩
    apply pullbackComparisonTarget_ext F
    · change (lift ≫ inv first) ≫ (first ≫ second) =
          targetComparison.toCodomain
      have liftCodomain : lift ≫ second =
          targetComparison.toCodomain :=
        congrArg (fun value ↦ value.toCodomain) liftComparison
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using
        liftCodomain
    · change (preFrobenioid F).base.map (lift ≫ inv first) =
          targetComparison.toBaseDomain
      have liftBase : (preFrobenioid F).base.map lift =
          targetComparison.toBaseDomain ≫
            (preFrobenioid F).base.map first :=
        congrArg (fun value ↦ value.toBaseDomain) liftComparison
      rw [(preFrobenioid F).base.map_comp, liftBase,
        Functor.map_inv, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]

/-- If a composite and its right factor are birational pullbacks and the
left factor has invertible base, then the left factor is an isomorphism. -/
theorem birational_isIso_of_comp_pullback_pullback_baseIso
    {source middle target : BirationalCategory F}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (compositePullback :
      (preFrobenioid F).IsPullback (first ≫ second))
    (secondPullback : (preFrobenioid F).IsPullback second)
    (firstBaseIso : (preFrobenioid F).IsBaseIso first) :
    IsIso first := by
  letI : IsIso ((preFrobenioid F).base.map first) := firstBaseIso
  let inverseComparison :
      (preFrobenioid F).PullbackComparisonTarget
        (first ≫ second) middle :=
    { toCodomain := second
      toBaseDomain := inv ((preFrobenioid F).base.map first)
      commutes := by
        rw [(preFrobenioid F).base.map_comp,
          IsIso.inv_hom_id_assoc] }
  obtain ⟨inverse, inverseComparisonEquality⟩ :=
    (compositePullback middle).2 inverseComparison
  have inverseComposite : inverse ≫ (first ≫ second) = second :=
    congrArg (fun value ↦ value.toCodomain)
      inverseComparisonEquality
  have inverseBase : (preFrobenioid F).base.map inverse =
      inv ((preFrobenioid F).base.map first) :=
    congrArg (fun value ↦ value.toBaseDomain)
      inverseComparisonEquality
  have inverseFirst : inverse ≫ first = 𝟙 middle := by
    apply (secondPullback middle).1
    apply pullbackComparisonTarget_ext F
    · change (inverse ≫ first) ≫ second = 𝟙 middle ≫ second
      simpa only [Category.assoc, Category.id_comp] using inverseComposite
    · change (preFrobenioid F).base.map (inverse ≫ first) =
          (preFrobenioid F).base.map (𝟙 middle)
      rw [(preFrobenioid F).base.map_comp, inverseBase,
        IsIso.inv_hom_id, (preFrobenioid F).base.map_id]
  have firstInverse : first ≫ inverse = 𝟙 source := by
    apply (compositePullback source).1
    apply pullbackComparisonTarget_ext F
    · change (first ≫ inverse) ≫ (first ≫ second) =
          𝟙 source ≫ (first ≫ second)
      rw [Category.assoc first inverse (first ≫ second),
        ← Category.assoc inverse first second, inverseFirst,
        Category.id_comp, Category.id_comp]
    · change (preFrobenioid F).base.map (first ≫ inverse) =
          (preFrobenioid F).base.map (𝟙 source)
      rw [(preFrobenioid F).base.map_comp, inverseBase,
        IsIso.hom_inv_id, (preFrobenioid F).base.map_id]
  exact IsIso.mk ⟨inverse, firstInverse, inverseFirst⟩

/-- Co-angularity in the birational target is invariant under
precomposition by an isomorphism. -/
theorem birational_isCoAngular_comp_iso_left_iff
    {source middle target : BirationalCategory F}
    (first : source ⟶ middle) (second : middle ⟶ target)
    [IsIso first] :
    (preFrobenioid F).IsCoAngular (first ≫ second) ↔
      (preFrobenioid F).IsCoAngular second := by
  constructor
  · intro compositeCoAngular U V gamma beta alpha equality
      alphaLinear betaPreStep betaIsometric baseAlternative
    apply compositeCoAngular (first ≫ gamma) beta alpha
    · simpa only [Category.assoc] using
        congrArg (fun value ↦ first ≫ value) equality
    · exact alphaLinear
    · exact betaPreStep
    · exact betaIsometric
    · rcases baseAlternative with alphaBaseIso | gammaBaseIso
      · exact Or.inl alphaBaseIso
      · right
        change IsIso ((preFrobenioid F).base.map (first ≫ gamma))
        rw [(preFrobenioid F).base.map_comp]
        haveI : IsIso ((preFrobenioid F).base.map first) := by
          infer_instance
        haveI : IsIso ((preFrobenioid F).base.map gamma) :=
          gammaBaseIso
        infer_instance
  · intro secondCoAngular U V gamma beta alpha equality
      alphaLinear betaPreStep betaIsometric baseAlternative
    apply secondCoAngular (inv first ≫ gamma) beta alpha
    · have adjusted := congrArg (fun value ↦ inv first ≫ value)
          equality
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using adjusted
    · exact alphaLinear
    · exact betaPreStep
    · exact betaIsometric
    · rcases baseAlternative with alphaBaseIso | gammaBaseIso
      · exact Or.inl alphaBaseIso
      · right
        change IsIso
          ((preFrobenioid F).base.map (inv first ≫ gamma))
        rw [(preFrobenioid F).base.map_comp]
        haveI : IsIso ((preFrobenioid F).base.map (inv first)) := by
          infer_instance
        haveI : IsIso ((preFrobenioid F).base.map gamma) :=
          gammaBaseIso
        infer_instance

/-- A source pullback remains a pullback after generic birational
localization.  Surjectivity lifts a right-fraction numerator through the
source pullback.  Injectivity refines two fractions to a common denominator
and then applies source pullback uniqueness. -/
theorem localization_map_isPullback_of_isPullback
    {source target : F.carrier} (arrow : source ⟶ target)
    (sourcePullback : F.preFrobenioid.IsPullback arrow) :
    (preFrobenioid F).IsPullback
      ((localizationFunctor F).map arrow) := by
  intro testObject
  obtain ⟨test, rfl⟩ :=
    (Localization.Construction.objEquiv (denominators F)).surjective
      testObject
  let localization := localizationFunctor F
  letI := hasRightCalculusOfFractions F
  constructor
  · intro first second comparisonEquality
    have codomainEquality :
        first ≫ localization.map arrow =
          second ≫ localization.map arrow :=
      congrArg (fun value ↦ value.toCodomain) comparisonEquality
    have baseEquality :
        (preFrobenioid F).base.map first =
          (preFrobenioid F).base.map second :=
      congrArg (fun value ↦ value.toBaseDomain) comparisonEquality
    obtain ⟨firstFraction, firstRepresents⟩ :=
      Localization.exists_rightFraction
        (L := localization) (W := denominators F) first
    obtain ⟨secondFraction, secondRepresents⟩ :=
      Localization.exists_rightFraction
        (L := localization) (W := denominators F) second
    let firstDenominator : CoAngularPreStepOver F test :=
      { source := firstFraction.X'
        hom := firstFraction.s
        property := firstFraction.hs }
    let secondDenominator : CoAngularPreStepOver F test :=
      { source := secondFraction.X'
        hom := secondFraction.s
        property := secondFraction.hs }
    have firstRoof :
        CoAngularPreStepOver.roofValue F firstDenominator firstFraction.f =
          first := by
      change firstFraction.map localization
          (MorphismProperty.Q_inverts (denominators F)) = first
      exact firstRepresents.symm
    have secondRoof :
        CoAngularPreStepOver.roofValue F secondDenominator secondFraction.f =
          second := by
      change secondFraction.map localization
          (MorphismProperty.Q_inverts (denominators F)) = second
      exact secondRepresents.symm
    have roofCompositeEquality :
        CoAngularPreStepOver.roofValue F firstDenominator
            (firstFraction.f ≫ arrow) =
          CoAngularPreStepOver.roofValue F secondDenominator
            (secondFraction.f ≫ arrow) := by
      rw [← roofValue_comp_localization_map,
        ← roofValue_comp_localization_map, firstRoof, secondRoof]
      exact codomainEquality
    unfold CoAngularPreStepOver.roofValue at roofCompositeEquality
    have fractionRelation :=
      (MorphismProperty.RightFraction.map_eq_iff
        (L := localization) (W := denominators F) _ _).1
        roofCompositeEquality
    rcases fractionRelation with
      ⟨commonSource, toFirst, toSecond, denominatorEquality,
        numeratorCompositeEquality, commonProperty⟩
    have firstBaseRoof := denominator_base_comp_roofValue_base F
      firstDenominator firstFraction.f
    have secondBaseRoof := denominator_base_comp_roofValue_base F
      secondDenominator secondFraction.f
    have firstBaseRoof' :
        F.preFrobenioid.base.map firstFraction.s ≫
            (preFrobenioid F).base.map first =
          F.preFrobenioid.base.map firstFraction.f := by
      simpa only [firstRoof] using firstBaseRoof
    have secondBaseRoof' :
        F.preFrobenioid.base.map secondFraction.s ≫
            (preFrobenioid F).base.map second =
          F.preFrobenioid.base.map secondFraction.f := by
      simpa only [secondRoof] using secondBaseRoof
    have commonDenominatorBaseEquality :
        F.preFrobenioid.base.map (toFirst ≫ firstFraction.s) =
          F.preFrobenioid.base.map (toSecond ≫ secondFraction.s) :=
      congrArg (fun value ↦ F.preFrobenioid.base.map value)
        denominatorEquality
    have commonBaseEquality :
        F.preFrobenioid.base.map (toFirst ≫ firstFraction.s) ≫
            (preFrobenioid F).base.map first =
          F.preFrobenioid.base.map (toSecond ≫ secondFraction.s) ≫
            (preFrobenioid F).base.map second :=
      (congrArg
        (fun value ↦ value ≫ (preFrobenioid F).base.map first)
        commonDenominatorBaseEquality).trans
        (congrArg
          (fun value ↦
            F.preFrobenioid.base.map
                (toSecond ≫ secondFraction.s) ≫ value)
          baseEquality)
    have refinedBaseEquality :
        F.preFrobenioid.base.map (toFirst ≫ firstFraction.f) =
          F.preFrobenioid.base.map (toSecond ≫ secondFraction.f) := by
      rw [F.preFrobenioid.base.map_comp,
        F.preFrobenioid.base.map_comp,
        ← firstBaseRoof', ← secondBaseRoof']
      simpa only [F.preFrobenioid.base.map_comp, Category.assoc] using
        commonBaseEquality
    have refinedNumeratorEquality :
        toFirst ≫ firstFraction.f =
          toSecond ≫ secondFraction.f := by
      apply (sourcePullback commonSource).1
      apply sourcePullbackComparisonTarget_ext F
      · change (toFirst ≫ firstFraction.f) ≫ arrow =
          (toSecond ≫ secondFraction.f) ≫ arrow
        simpa only [Category.assoc] using numeratorCompositeEquality
      · change F.preFrobenioid.base.map
            (toFirst ≫ firstFraction.f) =
          F.preFrobenioid.base.map (toSecond ≫ secondFraction.f)
        exact refinedBaseEquality
    have originalFractionRelation :
        MorphismProperty.RightFractionRel firstFraction secondFraction :=
      ⟨commonSource, toFirst, toSecond, denominatorEquality,
        refinedNumeratorEquality, commonProperty⟩
    have mappedFractionEquality :
        firstFraction.map localization
            (MorphismProperty.Q_inverts (denominators F)) =
          secondFraction.map localization
            (MorphismProperty.Q_inverts (denominators F)) :=
      (MorphismProperty.RightFraction.map_eq_iff
        (L := localization) (W := denominators F) _ _).2
        originalFractionRelation
    exact firstRepresents.trans
      (mappedFractionEquality.trans secondRepresents.symm)
  · intro targetComparison
    obtain ⟨fraction, fractionRepresents⟩ :=
      Localization.exists_rightFraction
        (L := localization) (W := denominators F)
        targetComparison.toCodomain
    let denominator : CoAngularPreStepOver F test :=
      { source := fraction.X'
        hom := fraction.s
        property := fraction.hs }
    have roofEquals :
        CoAngularPreStepOver.roofValue F denominator fraction.f =
          targetComparison.toCodomain := by
      change fraction.map localization
          (MorphismProperty.Q_inverts (denominators F)) =
        targetComparison.toCodomain
      exact fractionRepresents.symm
    have fractionCancellation :
        localization.map fraction.s ≫ targetComparison.toCodomain =
          localization.map fraction.f := by
      rw [← roofEquals]
      exact localization_map_denominator_comp_roofValue
        F denominator fraction.f
    have sourceCompatibility :
        F.preFrobenioid.base.map fraction.f =
          (F.preFrobenioid.base.map fraction.s ≫
              targetComparison.toBaseDomain) ≫
            F.preFrobenioid.base.map arrow := by
      have baseEquation := congrArg
        (fun value ↦ (preFrobenioid F).base.map value)
        fractionCancellation
      have targetCommutes := targetComparison.commutes
      dsimp only at baseEquation
      rw [localization_map_base F arrow] at targetCommutes
      rw [(preFrobenioid F).base.map_comp,
        localization_map_base F fraction.s,
        localization_map_base F fraction.f] at baseEquation
      have whiskeredTargetCommutes :
          F.preFrobenioid.base.map fraction.s ≫
              (preFrobenioid F).base.map targetComparison.toCodomain =
            F.preFrobenioid.base.map fraction.s ≫
              (targetComparison.toBaseDomain ≫
                F.preFrobenioid.base.map arrow) :=
        congrArg
          (fun value ↦ F.preFrobenioid.base.map fraction.s ≫ value)
          targetCommutes
      exact baseEquation.symm.trans
        (whiskeredTargetCommutes.trans (Category.assoc _ _ _).symm)
    let sourceComparison :
        F.preFrobenioid.PullbackComparisonTarget arrow fraction.X' :=
      { toCodomain := fraction.f
        toBaseDomain := F.preFrobenioid.base.map fraction.s ≫
          targetComparison.toBaseDomain
        commutes := sourceCompatibility }
    obtain ⟨lift, liftComparison⟩ :=
      (sourcePullback fraction.X').2 sourceComparison
    refine ⟨CoAngularPreStepOver.roofValue F denominator lift, ?_⟩
    apply pullbackComparisonTarget_ext F
    · change CoAngularPreStepOver.roofValue F denominator lift ≫
          localization.map arrow = targetComparison.toCodomain
      rw [roofValue_comp_localization_map]
      change CoAngularPreStepOver.roofValue F denominator
          (lift ≫ arrow) = targetComparison.toCodomain
      have sourceCodomain : lift ≫ arrow = fraction.f :=
        congrArg (fun value ↦ value.toCodomain) liftComparison
      rw [sourceCodomain, roofEquals]
    · have sourceBase :
          F.preFrobenioid.base.map lift =
            F.preFrobenioid.base.map fraction.s ≫
              targetComparison.toBaseDomain :=
        congrArg (fun value ↦ value.toBaseDomain) liftComparison
      have denominatorBaseIso :
          IsIso (F.preFrobenioid.base.map fraction.s) :=
        fraction.hs.1.2
      letI : IsIso (F.preFrobenioid.base.map fraction.s) :=
        denominatorBaseIso
      change (preFrobenioid F).base.map
          (CoAngularPreStepOver.roofValue F denominator lift) =
        targetComparison.toBaseDomain
      apply (cancel_epi (F.preFrobenioid.base.map fraction.s)).1
      rw [denominator_base_comp_roofValue_base F denominator lift,
        sourceBase]

/-- Proposition 4.4(iv): a source arrow becomes invertible in the generic
birational localization exactly when it is a co-angular pre-step. -/
theorem localization_map_isIso_iff_coAngularPreStep
    {source target : F.carrier} (arrow : source ⟶ target) :
    IsIso ((localizationFunctor F).map arrow) ↔
      denominators F arrow := by
  constructor
  · intro mappedIsIso
    letI := hasRightCalculusOfFractions F
    let localization := localizationFunctor F
    letI : IsIso (localization.map arrow) := mappedIsIso
    have mappedPreStep : (preFrobenioid F).IsPreStep
        (localization.map arrow) :=
      birational_isPreStep_of_isIso F (localization.map arrow) mappedIsIso
    have sourcePreStep : F.preFrobenioid.IsPreStep arrow :=
      (localization_map_isPreStep_iff F arrow).1 mappedPreStep
    obtain ⟨fraction, represents⟩ :=
      Localization.exists_rightFraction
        (L := localization) (W := denominators F)
        (inv (localization.map arrow))
    have denominatorCancellation :=
      MorphismProperty.RightFraction.map_s_comp_map fraction localization
        (MorphismProperty.Q_inverts (denominators F))
    have mappedComposite :
        localization.map (fraction.f ≫ arrow) =
          localization.map fraction.s := by
      rw [localization.map_comp]
      calc
        localization.map fraction.f ≫ localization.map arrow =
            (localization.map fraction.s ≫
              inv (localization.map arrow)) ≫
                localization.map arrow := by
          rw [represents]
          exact congrArg (fun value ↦ value ≫ localization.map arrow)
            denominatorCancellation.symm
        _ = localization.map fraction.s := by simp
    have sourceComposite : fraction.f ≫ arrow = fraction.s :=
      (localizationFunctor_faithful F).map_injective mappedComposite
    apply denominators_right_of_comp F fraction.f arrow
    · rw [sourceComposite]
      exact fraction.hs
    · exact sourcePreStep
  · intro denominator
    exact MorphismProperty.Q_inverts (denominators F) arrow denominator

/-- An arbitrary roof is invertible exactly when its numerator is a
co-angular pre-step. -/
theorem roofValue_isIso_iff
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    IsIso (CoAngularPreStepOver.roofValue F denominator numerator) ↔
      denominators F numerator := by
  haveI : IsIso ((localizationFunctor F).map denominator.hom) :=
    MorphismProperty.Q_inverts (denominators F) denominator.hom
      denominator.property
  constructor
  · intro roofIsIso
    letI : IsIso (CoAngularPreStepOver.roofValue F denominator numerator) :=
      roofIsIso
    have numeratorIsIso : IsIso ((localizationFunctor F).map numerator) := by
      rw [← localization_map_denominator_comp_roofValue F denominator numerator]
      infer_instance
    exact (localization_map_isIso_iff_coAngularPreStep F numerator).1
      numeratorIsIso
  · intro numeratorProperty
    have numeratorIsIso : IsIso ((localizationFunctor F).map numerator) :=
      (localization_map_isIso_iff_coAngularPreStep F numerator).2
        numeratorProperty
    letI : IsIso ((localizationFunctor F).map numerator) := numeratorIsIso
    exact IsIso.of_isIso_fac_left
      (localization_map_denominator_comp_roofValue F denominator numerator)

/-- The preservation direction of Proposition 4.4(iv)'s pullback
dictionary.  A co-angular linear arrow factors as a co-angular pre-step,
which localization inverts, followed by a source pullback. -/
theorem localization_map_isPullback_of_isCoAngular_linear
    {source target : F.carrier} (arrow : source ⟶ target)
    (sourceCoAngular : F.preFrobenioid.IsCoAngular arrow)
    (sourceLinear : F.preFrobenioid.IsLinear arrow) :
    (preFrobenioid F).IsPullback
      ((localizationFunctor F).map arrow) := by
  let factorization := Classical.choice (F.axioms.factorization arrow)
  let first := factorization.frobenius ≫ factorization.preStep
  have firstComposite : first ≫ factorization.pullback = arrow := by
    simpa only [first, Category.assoc] using factorization.composite
  have pullbackProperties := F.axioms.pullback_linear_lbInvertible
    factorization.pullback factorization.pullback_type
  have frobeniusLinear :
      F.preFrobenioid.IsLinear factorization.frobenius := by
    change F.preFrobenioid.frobeniusDegree factorization.frobenius = 1
    have degrees := congrArg F.preFrobenioid.frobeniusDegree
      factorization.composite
    rw [F.preFrobenioid.frobeniusDegree_comp,
      F.preFrobenioid.frobeniusDegree_comp,
      factorization.preStep_type.1, pullbackProperties.1,
      sourceLinear] at degrees
    simpa using degrees
  have frobeniusPreStep :
      F.preFrobenioid.IsPreStep factorization.frobenius :=
    ⟨frobeniusLinear, factorization.frobenius_type.2⟩
  have firstPreStep : F.preFrobenioid.IsPreStep first :=
    isPreStep_comp F factorization.frobenius factorization.preStep
      frobeniusPreStep factorization.preStep_type
  have firstBaseIso : F.preFrobenioid.IsBaseIso first := firstPreStep.2
  have compositeCoAngular :
      F.preFrobenioid.IsCoAngular
        (first ≫ factorization.pullback) := by
    rw [firstComposite]
    exact sourceCoAngular
  have firstCoAngular : F.preFrobenioid.IsCoAngular first :=
    FrobenioidRationalMonoidTransport.isCoAngular_left_of_comp_linear
      F first factorization.pullback firstBaseIso pullbackProperties.1
      compositeCoAngular
  have firstDenominator : denominators F first :=
    ⟨firstPreStep, firstCoAngular⟩
  have mappedFirstIso : IsIso ((localizationFunctor F).map first) :=
    (localization_map_isIso_iff_coAngularPreStep F first).2
      firstDenominator
  letI : IsIso ((localizationFunctor F).map first) := mappedFirstIso
  have mappedPullback :
      (preFrobenioid F).IsPullback
        ((localizationFunctor F).map factorization.pullback) :=
    localization_map_isPullback_of_isPullback F factorization.pullback
      factorization.pullback_type
  have mappedCompositePullback :=
    birational_isPullback_comp_of_isIso_left F
      ((localizationFunctor F).map first)
      ((localizationFunctor F).map factorization.pullback)
      mappedPullback
  rw [← (localizationFunctor F).map_comp,
    firstComposite] at mappedCompositePullback
  exact mappedCompositePullback

/-- The reflection direction of Proposition 4.4(iv)'s pullback dictionary.
A target pullback forces the non-pullback prefix in a source Frobenioid
factorization to become invertible, hence to be a co-angular pre-step. -/
theorem isCoAngular_and_linear_of_localization_map_isPullback
    {source target : F.carrier} (arrow : source ⟶ target)
    (mappedPullback : (preFrobenioid F).IsPullback
      ((localizationFunctor F).map arrow)) :
    F.preFrobenioid.IsCoAngular arrow ∧
      F.preFrobenioid.IsLinear arrow := by
  let factorization := Classical.choice (F.axioms.factorization arrow)
  let first := factorization.frobenius ≫ factorization.preStep
  have firstComposite : first ≫ factorization.pullback = arrow := by
    simpa only [first, Category.assoc] using factorization.composite
  have sourcePullbackProperties := F.axioms.pullback_linear_lbInvertible
    factorization.pullback factorization.pullback_type
  have mappedRightPullback :
      (preFrobenioid F).IsPullback
        ((localizationFunctor F).map factorization.pullback) :=
    localization_map_isPullback_of_isPullback F factorization.pullback
      factorization.pullback_type
  have mappedCompositePullback :
      (preFrobenioid F).IsPullback
        ((localizationFunctor F).map first ≫
          (localizationFunctor F).map factorization.pullback) := by
    rw [← (localizationFunctor F).map_comp,
      firstComposite]
    exact mappedPullback
  have firstBaseIso : F.preFrobenioid.IsBaseIso first := by
    change IsIso (F.preFrobenioid.base.map
      (factorization.frobenius ≫ factorization.preStep))
    rw [F.preFrobenioid.base.map_comp]
    haveI : IsIso
        (F.preFrobenioid.base.map factorization.frobenius) :=
      factorization.frobenius_type.2
    haveI : IsIso
        (F.preFrobenioid.base.map factorization.preStep) :=
      factorization.preStep_type.2
    infer_instance
  have mappedFirstBaseIso :
      (preFrobenioid F).IsBaseIso
        ((localizationFunctor F).map first) :=
    (localization_map_isBaseIso_iff F first).2 firstBaseIso
  have mappedFirstIso : IsIso ((localizationFunctor F).map first) :=
    birational_isIso_of_comp_pullback_pullback_baseIso F
      ((localizationFunctor F).map first)
      ((localizationFunctor F).map factorization.pullback)
      mappedCompositePullback mappedRightPullback mappedFirstBaseIso
  have firstDenominator : denominators F first :=
    (localization_map_isIso_iff_coAngularPreStep F first).1
      mappedFirstIso
  have compositeCoAngular : F.preFrobenioid.IsCoAngular
      (first ≫ factorization.pullback) :=
    F.axioms.coAngular_comp first factorization.pullback
      firstDenominator.2 sourcePullbackProperties.2.1
  have compositeLinear : F.preFrobenioid.IsLinear
      (first ≫ factorization.pullback) := by
    rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      firstDenominator.1.1, sourcePullbackProperties.1]
    rfl
  rw [firstComposite] at compositeCoAngular compositeLinear
  exact ⟨compositeCoAngular, compositeLinear⟩

/-- Proposition 4.4(iv): a localized source arrow is a pullback exactly
when the source arrow was co-angular and linear. -/
theorem localization_map_isPullback_iff
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).IsPullback
        ((localizationFunctor F).map arrow) ↔
      F.preFrobenioid.IsCoAngular arrow ∧
        F.preFrobenioid.IsLinear arrow :=
  ⟨isCoAngular_and_linear_of_localization_map_isPullback F arrow,
    fun hypothesis ↦ localization_map_isPullback_of_isCoAngular_linear
      F arrow hypothesis.1 hypothesis.2⟩

/-- Every arrow in the birational target is an isometry because the target
divisor monoid is terminal. -/
theorem isIsometric
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    (preFrobenioid F).IsIsometric arrow := by
  change (default : PUnit) = 0
  rfl

/-- Proposition 4.4(iv): every source arrow becomes an isometry after
birationalization. -/
theorem localization_map_isIsometric
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).IsIsometric ((localizationFunctor F).map arrow) :=
  isIsometric F _

/-- The preservation direction of Proposition 4.4(iv)'s co-angular
dictionary.  A target test factorization is lifted right-to-left through
right fractions; the middle pre-step is then split into its isometric and
co-angular factors before applying source co-angularity. -/
theorem localization_map_isCoAngular_of_isCoAngular
    {source target : F.carrier} (arrow : source ⟶ target)
    (sourceCoAngular : F.preFrobenioid.IsCoAngular arrow) :
    (preFrobenioid F).IsCoAngular
      ((localizationFunctor F).map arrow) := by
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    _betaIsometric baseAlternative
  obtain ⟨u, rfl⟩ :=
    (Localization.Construction.objEquiv (denominators F)).surjective U
  obtain ⟨v, rfl⟩ :=
    (Localization.Construction.objEquiv (denominators F)).surjective V
  let localization := localizationFunctor F
  letI := hasRightCalculusOfFractions F

  obtain ⟨alphaFraction, alphaRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localization) (W := denominators F) alpha
  let alphaDenominator : CoAngularPreStepOver F v :=
    { source := alphaFraction.X'
      hom := alphaFraction.s
      property := alphaFraction.hs }
  have alphaRoofEquals :
      CoAngularPreStepOver.roofValue F alphaDenominator alphaFraction.f =
        alpha := by
    change alphaFraction.map localization
        (MorphismProperty.Q_inverts (denominators F)) = alpha
    exact alphaRepresents.symm
  have alphaNumeratorLinear :
      F.preFrobenioid.IsLinear alphaFraction.f := by
    apply (roofValue_isLinear_iff F alphaDenominator alphaFraction.f).1
    rw [alphaRoofEquals]
    exact alphaLinear
  have alphaCancellation :
      localization.map alphaFraction.s ≫ alpha =
        localization.map alphaFraction.f := by
    rw [← alphaRoofEquals]
    exact localization_map_denominator_comp_roofValue
      F alphaDenominator alphaFraction.f
  let alphaIso := Localization.isoOfHom localization (denominators F)
    alphaFraction.s alphaFraction.hs

  let betaAdjusted := beta ≫ alphaIso.inv
  have betaAdjustedPreStep :
      (preFrobenioid F).IsPreStep betaAdjusted := by
    apply birational_isPreStep_comp F beta
      alphaIso.inv betaPreStep
    exact birational_isPreStep_of_isIso F
      alphaIso.inv inferInstance
  obtain ⟨betaFraction, betaRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localization) (W := denominators F) betaAdjusted
  let betaDenominator : CoAngularPreStepOver F u :=
    { source := betaFraction.X'
      hom := betaFraction.s
      property := betaFraction.hs }
  have betaRoofEquals :
      CoAngularPreStepOver.roofValue F betaDenominator betaFraction.f =
        betaAdjusted := by
    change betaFraction.map localization
        (MorphismProperty.Q_inverts (denominators F)) = betaAdjusted
    exact betaRepresents.symm
  have betaNumeratorPreStep :
      F.preFrobenioid.IsPreStep betaFraction.f := by
    apply (roofValue_isPreStep_iff F betaDenominator betaFraction.f).1
    rw [betaRoofEquals]
    exact betaAdjustedPreStep
  let middleFactorization := Classical.choice
    (F.axioms.preStep_isometricThenCoAngular
      betaFraction.f betaNumeratorPreStep)
  have middleFirstIsometric :
      F.preFrobenioid.IsIsometric middleFactorization.first := by
    exact middleFactorization.first_kind
  have middleSecondCoAngular :
      F.preFrobenioid.IsCoAngular middleFactorization.second := by
    exact middleFactorization.second_kind
  have middleSecondDenominator :
      denominators F middleFactorization.second :=
    ⟨middleFactorization.second_preStep, middleSecondCoAngular⟩
  let middleSecondIso := Localization.isoOfHom localization (denominators F)
    middleFactorization.second middleSecondDenominator
  let rightInternalIso := middleSecondIso ≪≫ alphaIso
  let rightInternal := rightInternalIso.hom
  have rightNaturality :
      rightInternal ≫ alpha =
        localization.map
          (middleFactorization.second ≫ alphaFraction.f) := by
    change (localization.map middleFactorization.second ≫
      localization.map alphaFraction.s) ≫ alpha =
        localization.map
          (middleFactorization.second ≫ alphaFraction.f)
    rw [Category.assoc, alphaCancellation, localization.map_comp]

  have betaCancellation :
      localization.map betaFraction.s ≫ betaAdjusted =
        localization.map betaFraction.f := by
    rw [← betaRoofEquals]
    exact localization_map_denominator_comp_roofValue
      F betaDenominator betaFraction.f
  let betaIso := Localization.isoOfHom localization (denominators F)
    betaFraction.s betaFraction.hs
  have middleNaturality :
      betaIso.hom ≫ beta =
        localization.map middleFactorization.first ≫ rightInternal := by
    apply (cancel_mono alphaIso.inv).1
    calc
      (betaIso.hom ≫ beta) ≫ alphaIso.inv =
        localization.map betaFraction.s ≫ betaAdjusted := by
          change (localization.map betaFraction.s ≫ beta) ≫
              alphaIso.inv =
            localization.map betaFraction.s ≫
              (beta ≫ alphaIso.inv)
          exact Category.assoc _ _ _
      _ = localization.map betaFraction.f := betaCancellation
      _ = localization.map
          (middleFactorization.first ≫ middleFactorization.second) := by
        rw [middleFactorization.composite]
      _ = localization.map middleFactorization.first ≫
          localization.map middleFactorization.second :=
        localization.map_comp _ _
      _ = (localization.map middleFactorization.first ≫ rightInternal) ≫
          alphaIso.inv := by
        change localization.map middleFactorization.first ≫
            localization.map middleFactorization.second =
          (localization.map middleFactorization.first ≫
            (localization.map middleFactorization.second ≫ alphaIso.hom)) ≫
              alphaIso.inv
        simp only [Category.assoc, alphaIso.hom_inv_id,
          Category.comp_id]

  let gammaAdjusted := gamma ≫ betaIso.inv
  obtain ⟨gammaFraction, gammaRepresents⟩ :=
    Localization.exists_rightFraction
      (L := localization) (W := denominators F) gammaAdjusted
  let gammaDenominator : CoAngularPreStepOver F source :=
    { source := gammaFraction.X'
      hom := gammaFraction.s
      property := gammaFraction.hs }
  have gammaRoofEquals :
      CoAngularPreStepOver.roofValue F gammaDenominator gammaFraction.f =
        gammaAdjusted := by
    change gammaFraction.map localization
        (MorphismProperty.Q_inverts (denominators F)) = gammaAdjusted
    exact gammaRepresents.symm
  have gammaCancellation :
      localization.map gammaFraction.s ≫ gammaAdjusted =
        localization.map gammaFraction.f := by
    rw [← gammaRoofEquals]
    exact localization_map_denominator_comp_roofValue
      F gammaDenominator gammaFraction.f
  have leftNaturality :
      localization.map gammaFraction.s ≫ gamma =
        localization.map gammaFraction.f ≫
          betaIso.hom := by
    apply (cancel_mono betaIso.inv).1
    calc
      (localization.map gammaFraction.s ≫ gamma) ≫
          betaIso.inv =
        localization.map gammaFraction.s ≫ gammaAdjusted := by
          change (localization.map gammaFraction.s ≫ gamma) ≫
              betaIso.inv =
            localization.map gammaFraction.s ≫
              (gamma ≫ betaIso.inv)
          exact Category.assoc _ _ _
      _ = localization.map gammaFraction.f := gammaCancellation
      _ = (localization.map gammaFraction.f ≫
          betaIso.hom) ≫
            betaIso.inv := by
        simp only [Category.assoc, betaIso.hom_inv_id,
          Category.comp_id]

  let sourceAlpha := middleFactorization.second ≫ alphaFraction.f
  have sourceAlphaLinear : F.preFrobenioid.IsLinear sourceAlpha := by
    rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      middleFactorization.second_preStep.1, alphaNumeratorLinear]
    rfl
  have sourceBaseAlternative :
      F.preFrobenioid.IsBaseIso sourceAlpha ∨
        F.preFrobenioid.IsBaseIso gammaFraction.f := by
    rcases baseAlternative with alphaBaseIso | gammaBaseIso
    · left
      have alphaNumeratorBaseIso :
          F.preFrobenioid.IsBaseIso alphaFraction.f :=
        (roofValue_isBaseIso_iff F alphaDenominator alphaFraction.f).1
          (by rw [alphaRoofEquals]; exact alphaBaseIso)
      change IsIso (F.preFrobenioid.base.map sourceAlpha)
      rw [F.preFrobenioid.base.map_comp]
      haveI : IsIso
          (F.preFrobenioid.base.map middleFactorization.second) :=
        middleFactorization.second_preStep.2
      haveI : IsIso (F.preFrobenioid.base.map alphaFraction.f) :=
        alphaNumeratorBaseIso
      infer_instance
    · right
      have adjustedBaseIso :
          (preFrobenioid F).IsBaseIso gammaAdjusted := by
        change IsIso ((preFrobenioid F).base.map gammaAdjusted)
        dsimp only [gammaAdjusted]
        rw [(preFrobenioid F).base.map_comp]
        haveI : IsIso ((preFrobenioid F).base.map gamma) := gammaBaseIso
        infer_instance
      exact (roofValue_isBaseIso_iff F gammaDenominator gammaFraction.f).1
        (by rw [gammaRoofEquals]; exact adjustedBaseIso)

  have mappedSourceEquality :
      localization.map (gammaFraction.s ≫ arrow) =
        localization.map
          (gammaFraction.f ≫ middleFactorization.first ≫ sourceAlpha) := by
    rw [localization.map_comp, localization.map_comp,
      localization.map_comp]
    calc
      localization.map gammaFraction.s ≫ localization.map arrow =
          (localization.map gammaFraction.s ≫ gamma) ≫ beta ≫ alpha := by
        simpa only [Category.assoc] using
          congrArg (fun value ↦ localization.map gammaFraction.s ≫ value)
            equality.symm
      _ = (localization.map gammaFraction.f ≫
            betaIso.hom) ≫ beta ≫ alpha := by
        exact congrArg (fun value ↦ value ≫ beta ≫ alpha) leftNaturality
      _ = localization.map gammaFraction.f ≫
            ((betaIso.hom ≫ beta) ≫ alpha) := by
        simp only [Category.assoc]
      _ = localization.map gammaFraction.f ≫
            ((localization.map middleFactorization.first ≫ rightInternal) ≫
              alpha) :=
        congrArg
          (fun value ↦ localization.map gammaFraction.f ≫ value ≫ alpha)
          middleNaturality
      _ = localization.map gammaFraction.f ≫
            localization.map middleFactorization.first ≫
              localization.map sourceAlpha := by
        simp only [Category.assoc]
        rw [rightNaturality]
  have sourceEquality :
      gammaFraction.s ≫ arrow =
        gammaFraction.f ≫ middleFactorization.first ≫ sourceAlpha :=
    (localizationFunctor_faithful F).map_injective mappedSourceEquality
  have sourceCompositeCoAngular :
      F.preFrobenioid.IsCoAngular (gammaFraction.s ≫ arrow) :=
    F.axioms.coAngular_comp gammaFraction.s arrow
      gammaFraction.hs.2 sourceCoAngular
  have middleIso : IsIso middleFactorization.first :=
    sourceCompositeCoAngular gammaFraction.f middleFactorization.first
      sourceAlpha sourceEquality.symm sourceAlphaLinear
      middleFactorization.first_preStep middleFirstIsometric
      sourceBaseAlternative
  haveI : IsIso middleFactorization.first := middleIso
  have mappedMiddleIso : IsIso
      (localization.map middleFactorization.first) := by infer_instance
  have rightCompositeIso : IsIso
      (localization.map middleFactorization.first ≫ rightInternal) :=
    IsIso.comp_isIso' mappedMiddleIso rightInternalIso.isIso_hom
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    betaIso.isIso_hom rightCompositeIso middleNaturality

/-- The preservation direction of Proposition 4.4(iv)'s isotropic-object
dictionary. -/
theorem localization_obj_isIsotropic_of_isIsotropic
    (object : F.carrier)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic object) :
    (preFrobenioid F).IsIsotropic
      ((localizationFunctor F).obj object) := by
  intro target arrow arrowPreStep _arrowIsometric
  obtain ⟨targetSource, rfl⟩ :=
    (Localization.Construction.objEquiv (denominators F)).surjective target
  letI := hasRightCalculusOfFractions F
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F object :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  have roofEquals :
      CoAngularPreStepOver.roofValue F denominator fraction.f = arrow := by
    change fraction.map (localizationFunctor F)
        (MorphismProperty.Q_inverts (denominators F)) = arrow
    exact represents.symm
  have numeratorPreStep :
      F.preFrobenioid.IsPreStep fraction.f := by
    apply (roofValue_isPreStep_iff F denominator fraction.f).1
    rw [roofEquals]
    exact arrowPreStep
  have denominatorSourceIsotropic :
      F.preFrobenioid.IsIsotropic denominator.source :=
    (FrobenioidRationalMonoidTransport.isIsotropic_source_iff_target_of_coAngular_linear
        F denominator.hom denominator.property.2 denominator.property.1.1).2
      sourceIsotropic
  have numeratorCoAngular :
      F.preFrobenioid.IsCoAngular fraction.f :=
    FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F fraction.f denominatorSourceIsotropic
  have roofIso : IsIso
      (CoAngularPreStepOver.roofValue F denominator fraction.f) :=
    (roofValue_isIso_iff F denominator fraction.f).2
      ⟨numeratorPreStep, numeratorCoAngular⟩
  rw [← roofEquals]
  exact roofIso

/-- The reflection direction of Proposition 4.4(iv)'s co-angular
dictionary: if a source arrow is co-angular after birationalization, then it
was already co-angular. -/
theorem isCoAngular_of_localization_map_isCoAngular
    {source target : F.carrier} (arrow : source ⟶ target)
    (mappedCoAngular : (preFrobenioid F).IsCoAngular
      ((localizationFunctor F).map arrow)) :
    F.preFrobenioid.IsCoAngular arrow := by
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  have mappedEquality :
      (localizationFunctor F).map gamma ≫
          (localizationFunctor F).map beta ≫
            (localizationFunctor F).map alpha =
        (localizationFunctor F).map arrow := by
    simpa only [(localizationFunctor F).map_comp] using
      congrArg (fun value ↦ (localizationFunctor F).map value) equality
  have mappedBaseAlternative :
      (preFrobenioid F).IsBaseIso ((localizationFunctor F).map alpha) ∨
        (preFrobenioid F).IsBaseIso
          ((localizationFunctor F).map gamma) := by
    rcases baseAlternative with alphaBaseIso | gammaBaseIso
    · exact Or.inl
        ((localization_map_isBaseIso_iff F alpha).2 alphaBaseIso)
    · exact Or.inr
        ((localization_map_isBaseIso_iff F gamma).2 gammaBaseIso)
  have mappedBetaIso : IsIso ((localizationFunctor F).map beta) :=
    mappedCoAngular
      ((localizationFunctor F).map gamma)
      ((localizationFunctor F).map beta)
      ((localizationFunctor F).map alpha)
      mappedEquality
      ((localization_map_isLinear_iff F alpha).2 alphaLinear)
      ((localization_map_isPreStep_iff F beta).2 betaPreStep)
      (localization_map_isIsometric F beta)
      mappedBaseAlternative
  have betaDenominator : denominators F beta :=
    (localization_map_isIso_iff_coAngularPreStep F beta).1 mappedBetaIso
  exact
    FrobenioidRationalMonoidTransport.isIso_of_coAngular_isometric_preStep
      F beta betaPreStep betaDenominator.2 betaIsometric

/-- The reflection direction of Proposition 4.4(iv)'s Frobenius-type
dictionary.  A source arrow that becomes Frobenius-type was co-angular and
had invertible base before localization. -/
theorem isCoAngular_and_isBaseIso_of_localization_map_isOfFrobeniusType
    {source target : F.carrier} (arrow : source ⟶ target)
    (mappedFrobeniusType : (preFrobenioid F).IsOfFrobeniusType
      ((localizationFunctor F).map arrow)) :
    F.preFrobenioid.IsCoAngular arrow ∧
      F.preFrobenioid.IsBaseIso arrow :=
  ⟨isCoAngular_of_localization_map_isCoAngular F arrow
      mappedFrobeniusType.1.1,
    (localization_map_isBaseIso_iff F arrow).1 mappedFrobeniusType.2⟩

/-- Proposition 4.4(iv): localization preserves and reflects co-angular
source arrows for an arbitrary Frobenioid. -/
theorem localization_map_isCoAngular_iff
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).IsCoAngular ((localizationFunctor F).map arrow) ↔
      F.preFrobenioid.IsCoAngular arrow :=
  ⟨isCoAngular_of_localization_map_isCoAngular F arrow,
    localization_map_isCoAngular_of_isCoAngular F arrow⟩

/-- Proposition 4.4(iv): a source arrow becomes Frobenius-type exactly
when it was co-angular with invertible base. -/
theorem localization_map_isOfFrobeniusType_iff
    {source target : F.carrier} (arrow : source ⟶ target) :
    (preFrobenioid F).IsOfFrobeniusType
        ((localizationFunctor F).map arrow) ↔
      F.preFrobenioid.IsCoAngular arrow ∧
        F.preFrobenioid.IsBaseIso arrow := by
  constructor
  · exact isCoAngular_and_isBaseIso_of_localization_map_isOfFrobeniusType
      F arrow
  · rintro ⟨coAngular, baseIso⟩
    exact
      ⟨⟨localization_map_isCoAngular_of_isCoAngular F arrow coAngular,
          localization_map_isIsometric F arrow⟩,
        (localization_map_isBaseIso_iff F arrow).2 baseIso⟩

/-- An arbitrary right-fraction roof is co-angular exactly when its source
numerator is co-angular. -/
theorem roofValue_isCoAngular_iff
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (preFrobenioid F).IsCoAngular
        (CoAngularPreStepOver.roofValue F denominator numerator) ↔
      F.preFrobenioid.IsCoAngular numerator := by
  have denominatorIso : IsIso
      ((localizationFunctor F).map denominator.hom) :=
    MorphismProperty.Q_inverts (denominators F) denominator.hom
      denominator.property
  letI : IsIso ((localizationFunctor F).map denominator.hom) :=
    denominatorIso
  change (preFrobenioid F).IsCoAngular
      (inv ((localizationFunctor F).map denominator.hom) ≫
        (localizationFunctor F).map numerator) ↔
    F.preFrobenioid.IsCoAngular numerator
  rw [birational_isCoAngular_comp_iso_left_iff,
    localization_map_isCoAngular_iff]

/-- An arbitrary right-fraction roof is Frobenius-type exactly when its
source numerator is co-angular with invertible base. -/
theorem roofValue_isOfFrobeniusType_iff
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (preFrobenioid F).IsOfFrobeniusType
        (CoAngularPreStepOver.roofValue F denominator numerator) ↔
      F.preFrobenioid.IsCoAngular numerator ∧
        F.preFrobenioid.IsBaseIso numerator := by
  change
    (((preFrobenioid F).IsCoAngular
          (CoAngularPreStepOver.roofValue F denominator numerator) ∧
        (preFrobenioid F).IsIsometric
          (CoAngularPreStepOver.roofValue F denominator numerator)) ∧
      (preFrobenioid F).IsBaseIso
        (CoAngularPreStepOver.roofValue F denominator numerator)) ↔ _
  rw [roofValue_isCoAngular_iff F denominator numerator,
    roofValue_isBaseIso_iff F denominator numerator]
  simp only [isIsometric F
    (CoAngularPreStepOver.roofValue F denominator numerator), and_true]

/-- An arbitrary right-fraction roof is a pullback exactly when its source
numerator is co-angular and linear. -/
theorem roofValue_isPullback_iff
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (preFrobenioid F).IsPullback
        (CoAngularPreStepOver.roofValue F denominator numerator) ↔
      F.preFrobenioid.IsCoAngular numerator ∧
        F.preFrobenioid.IsLinear numerator := by
  have denominatorIso : IsIso
      ((localizationFunctor F).map denominator.hom) :=
    MorphismProperty.Q_inverts (denominators F) denominator.hom
      denominator.property
  letI : IsIso ((localizationFunctor F).map denominator.hom) :=
    denominatorIso
  constructor
  · intro roofPullback
    have numeratorPullback :
        (preFrobenioid F).IsPullback
          ((localizationFunctor F).map denominator.hom ≫
            CoAngularPreStepOver.roofValue F denominator numerator) :=
      birational_isPullback_comp_of_isIso_left F
        ((localizationFunctor F).map denominator.hom)
        (CoAngularPreStepOver.roofValue F denominator numerator)
        roofPullback
    rw [localization_map_denominator_comp_roofValue F denominator numerator]
      at numeratorPullback
    exact (localization_map_isPullback_iff F numerator).1
      numeratorPullback
  · intro numeratorProperties
    have numeratorPullback :
        (preFrobenioid F).IsPullback
          ((localizationFunctor F).map numerator) :=
      (localization_map_isPullback_iff F numerator).2
        numeratorProperties
    change (preFrobenioid F).IsPullback
      (inv ((localizationFunctor F).map denominator.hom) ≫
        (localizationFunctor F).map numerator)
    exact birational_isPullback_comp_of_isIso_left F
      (inv ((localizationFunctor F).map denominator.hom))
      ((localizationFunctor F).map numerator) numeratorPullback

/-- The reflection direction of Proposition 4.4(iv)'s isotropic-object
dictionary. -/
theorem isIsotropic_of_localization_obj_isIsotropic
    (object : F.carrier)
    (mappedIsotropic : (preFrobenioid F).IsIsotropic
      ((localizationFunctor F).obj object)) :
    F.preFrobenioid.IsIsotropic object := by
  intro target arrow preStep isometric
  have mappedArrowIso : IsIso ((localizationFunctor F).map arrow) :=
    mappedIsotropic
      ((localizationFunctor F).map arrow)
      ((localization_map_isPreStep_iff F arrow).2 preStep)
      (localization_map_isIsometric F arrow)
  have denominator : denominators F arrow :=
    (localization_map_isIso_iff_coAngularPreStep F arrow).1 mappedArrowIso
  exact
    FrobenioidRationalMonoidTransport.isIso_of_coAngular_isometric_preStep
      F arrow preStep denominator.2 isometric

/-- Proposition 4.4(iv): localization preserves and reflects isotropic
objects for an arbitrary Frobenioid. -/
theorem localization_obj_isIsotropic_iff
    (object : F.carrier) :
    (preFrobenioid F).IsIsotropic
        ((localizationFunctor F).obj object) ↔
      F.preFrobenioid.IsIsotropic object :=
  ⟨isIsotropic_of_localization_obj_isIsotropic F object,
    localization_obj_isIsotropic_of_isIsotropic F object⟩

end

end Iut.FrobenioidBirationalization
