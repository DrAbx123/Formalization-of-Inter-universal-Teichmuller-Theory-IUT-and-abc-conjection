/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidCoAngularBaseChange

open CategoryTheory

/-!
# Pullback lifts of base arrows in a Frobenioid

This file isolates the Definition 1.3(i)(c) input used in Frobenioids I,
Proposition 2.2(ii).  Every arrow between the bases of isotropic objects is
represented, after an isomorphism at its source, by an actual pullback arrow
whose source is again isotropic.
-/

namespace Iut.FrobenioidBasePullbackLift

universe u

noncomputable section

variable (F : FrobenioidPresentation.{u})

private theorem hom_eq_of_pullback
    {T X Y : F.carrier} (arrow : X ⟶ Y)
    (pullback : F.preFrobenioid.IsPullback arrow)
    (left right : T ⟶ X)
    (composite : left ≫ arrow = right ≫ arrow)
    (base : F.preFrobenioid.base.map left =
      F.preFrobenioid.base.map right) : left = right := by
  apply (pullback T).1
  change
    ({ toCodomain := left ≫ arrow
       toBaseDomain := F.preFrobenioid.base.map left
       commutes := by simp } :
      F.preFrobenioid.PullbackComparisonTarget arrow T) =
    ({ toCodomain := right ≫ arrow
       toBaseDomain := F.preFrobenioid.base.map right
       commutes := by simp } :
      F.preFrobenioid.PullbackComparisonTarget arrow T)
  rw [PreFrobenioid.PullbackComparisonTarget.mk.injEq]
  exact ⟨composite, base⟩

/-- Identity arrows are pullback arrows. -/
theorem isPullback_id (object : F.carrier) :
    F.preFrobenioid.IsPullback (𝟙 object) := by
  intro test
  constructor
  · intro left right equality
    simpa [PreFrobenioid.pullbackComparison] using congrArg
      PreFrobenioid.PullbackComparisonTarget.toCodomain equality
  · intro target
    refine ⟨target.toCodomain, ?_⟩
    rw [PreFrobenioid.PullbackComparisonTarget.mk.injEq]
    exact
      ⟨by simp [PreFrobenioid.pullbackComparison],
        by simpa [PreFrobenioid.pullbackComparison] using
          target.commutes⟩

/-- Composites of pullback arrows are pullback arrows. -/
theorem isPullback_comp
    {source middle target : F.carrier}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstPullback : F.preFrobenioid.IsPullback first)
    (secondPullback : F.preFrobenioid.IsPullback second) :
    F.preFrobenioid.IsPullback (first ≫ second) := by
  intro test
  constructor
  · intro left right equality
    have compositeEquality :
        (left ≫ first) ≫ second = (right ≫ first) ≫ second := by
      simpa [PreFrobenioid.pullbackComparison, Category.assoc] using congrArg
        PreFrobenioid.PullbackComparisonTarget.toCodomain equality
    have baseEquality :
        F.preFrobenioid.base.map left =
          F.preFrobenioid.base.map right :=
      congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain equality
    have firstCompositeEquality : left ≫ first = right ≫ first := by
      apply hom_eq_of_pullback F second secondPullback
      · exact compositeEquality
      · rw [F.preFrobenioid.base.map_comp,
          F.preFrobenioid.base.map_comp, baseEquality]
    exact hom_eq_of_pullback F first firstPullback left right
      firstCompositeEquality baseEquality
  · intro comparison
    let secondTarget :
        F.preFrobenioid.PullbackComparisonTarget second test :=
      { toCodomain := comparison.toCodomain
        toBaseDomain :=
          comparison.toBaseDomain ≫ F.preFrobenioid.base.map first
        commutes := by
          rw [comparison.commutes,
            F.preFrobenioid.base.map_comp, Category.assoc] }
    let throughSecond := Classical.choose
      ((secondPullback test).2 secondTarget)
    have throughSecondSpec := Classical.choose_spec
      ((secondPullback test).2 secondTarget)
    let firstTarget :
        F.preFrobenioid.PullbackComparisonTarget first test :=
      { toCodomain := throughSecond
        toBaseDomain := comparison.toBaseDomain
        commutes := by
          exact congrArg
            PreFrobenioid.PullbackComparisonTarget.toBaseDomain
            throughSecondSpec }
    let lift := Classical.choose
      ((firstPullback test).2 firstTarget)
    have liftSpec := Classical.choose_spec
      ((firstPullback test).2 firstTarget)
    refine ⟨lift, ?_⟩
    rw [PreFrobenioid.PullbackComparisonTarget.mk.injEq]
    constructor
    · change lift ≫ (first ≫ second) = comparison.toCodomain
      rw [← Category.assoc]
      have liftToMiddle : lift ≫ first = throughSecond := by
        simpa [lift, throughSecond, PreFrobenioid.pullbackComparison,
          firstTarget] using
          congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
            liftSpec
      have middleToTarget :
          throughSecond ≫ second = comparison.toCodomain := by
        simpa [throughSecond, PreFrobenioid.pullbackComparison,
          secondTarget] using
          congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
            throughSecondSpec
      rw [liftToMiddle, middleToTarget]
    · simpa [lift, PreFrobenioid.pullbackComparison, firstTarget] using
        congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain
          liftSpec

/-- A Definition 1.3(i)(c) pullback representative of a base arrow between
isotropic objects. -/
structure BaseArrowLift
    (source target : FrobenioidIsotropicBase.DStar F)
    (baseArrow :
      F.preFrobenioid.base.obj source.object ⟶
        F.preFrobenioid.base.obj target.object) where
  liftedSource : F.carrier
  liftedSource_isotropic :
    F.preFrobenioid.IsIsotropic liftedSource
  liftedArrow : liftedSource ⟶ target.object
  liftedArrow_pullback :
    F.preFrobenioid.IsPullback liftedArrow
  liftedArrow_linear :
    F.preFrobenioid.IsLinear liftedArrow
  liftedArrow_coAngular :
    F.preFrobenioid.IsCoAngular liftedArrow
  sourceBaseIso :
    F.preFrobenioid.base.obj liftedSource ≅
      F.preFrobenioid.base.obj source.object
  base_triangle :
    sourceBaseIso.hom ≫ baseArrow =
      F.preFrobenioid.base.map liftedArrow

/-- Definition 1.3(i)(c) supplies a pullback representative of every base
arrow.  Proposition 1.4(ii) and Proposition 1.9(iv) make its source isotropic.
-/
def baseArrowLift
    (source target : FrobenioidIsotropicBase.DStar F)
    (baseArrow :
      F.preFrobenioid.base.obj source.object ⟶
        F.preFrobenioid.base.obj target.object) :
    BaseArrowLift F source target baseArrow := by
  let requested : F.preFrobenioid.BaseSliceObject target.object :=
    { source := F.preFrobenioid.base.obj source.object
      hom := baseArrow }
  let existence :=
    (F.axioms.pullbackBaseSlices target.object).essentiallySurjective
      requested
  let representative := Classical.choose existence
  have representativeProperties := Classical.choose_spec existence
  have representativePullback := representativeProperties.1
  let comparison := Classical.choice representativeProperties.2
  have pullbackProperties :=
    F.axioms.pullback_linear_lbInvertible representative.hom
      representativePullback
  have sourceIsotropic :
      F.preFrobenioid.IsIsotropic representative.source :=
    Iut.FrobenioidRationalMonoidTransport.isIsotropic_source_of_coAngular_linear
        F representative.hom
        pullbackProperties.2.1 pullbackProperties.1 target.isotropic
  exact
    { liftedSource := representative.source
      liftedSource_isotropic := sourceIsotropic
      liftedArrow := representative.hom
      liftedArrow_pullback := representativePullback
      liftedArrow_linear := pullbackProperties.1
      liftedArrow_coAngular := pullbackProperties.2.1
      sourceBaseIso := comparison.iso
      base_triangle := comparison.hom_commutes }

/-- On a co-angular pre-step, Proposition 1.11(iv)'s pullback is the inverse
of Definition 1.3(iii)(c)'s unit transport. -/
theorem linearEndomorphismPullbackHom_preStep
    {source target : F.carrier} (arrow : source ⟶ target)
    (preStep : F.preFrobenioid.IsPreStep arrow)
    (coAngular : F.preFrobenioid.IsCoAngular arrow)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic source) :
    Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
        F arrow preStep.1 sourceIsotropic =
      (F.axioms.unitTransport arrow preStep coAngular).transport.symm.toMonoidHom := by
  apply MonoidHom.ext
  intro value
  symm
  apply Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback_unique
    F arrow preStep.1 sourceIsotropic
  have relation :=
    (F.axioms.unitTransport arrow preStep coAngular).conjugates
      ((F.axioms.unitTransport arrow preStep coAngular).transport.symm value)
  simpa using relation

/-- The base isomorphism underlying a pre-step. -/
def preStepBaseIso
    {source target : F.carrier} (arrow : source ⟶ target)
    (preStep : F.preFrobenioid.IsPreStep arrow) :
    F.preFrobenioid.base.obj source ≅
      F.preFrobenioid.base.obj target := by
  letI : IsIso (F.preFrobenioid.base.map arrow) := preStep.2
  exact asIso (F.preFrobenioid.base.map arrow)

/-- A pre-step and an identity leg form a common witness for its underlying
base isomorphism. -/
def preStepWitness
    (source target : FrobenioidIsotropicBase.DStar F)
    (arrow : source.object ⟶ target.object)
    (preStep : F.preFrobenioid.IsPreStep arrow)
    (coAngular : F.preFrobenioid.IsCoAngular arrow) :
    Iut.FrobenioidCoAngularBaseChange.CommonCoAngularPreStepWitness F
      source target (preStepBaseIso F arrow preStep) where
  midpoint := source.object
  midpoint_isotropic := source.isotropic
  toLeft := 𝟙 source.object
  toRight := arrow
  toLeft_preStep :=
    Iut.FrobenioidCoAngularBaseChange.isPreStep_of_isIso F
      (𝟙 source.object)
  toRight_preStep := preStep
  toLeft_coAngular :=
    Iut.FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F (𝟙 source.object) source.isotropic
  toRight_coAngular := coAngular
  leftBaseInverse := 𝟙 _
  leftBaseInverse_hom := by simp
  hom_leftBaseInverse := by simp
  comparison := by
    simp [preStepBaseIso]

/-- Canonical base-isomorphism transport agrees with covariant unit transport
on every co-angular pre-step. -/
theorem baseIsoRationalMonoidEquiv_preStep
    (source target : FrobenioidIsotropicBase.DStar F)
    (arrow : source.object ⟶ target.object)
    (preStep : F.preFrobenioid.IsPreStep arrow)
    (coAngular : F.preFrobenioid.IsCoAngular arrow) :
    Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        source target (preStepBaseIso F arrow preStep) =
      (F.axioms.unitTransport arrow preStep coAngular).transport := by
  let witness := preStepWitness F source target arrow preStep coAngular
  have selectedIdentity := F.axioms.unitTransport_unique
    (𝟙 source.object) witness.toLeft_preStep witness.toLeft_coAngular
    (F.axioms.unitTransport (𝟙 source.object)
      witness.toLeft_preStep witness.toLeft_coAngular)
    (Iut.FrobenioidCoAngularBaseChange.identityUnitTransport F source.object)
  calc
    Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          source target (preStepBaseIso F arrow preStep) =
        witness.rationalMonoidEquiv :=
      (Iut.FrobenioidCoAngularBaseChange.rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv
        F witness).symm
    _ = (F.axioms.unitTransport arrow preStep coAngular).transport := by
      apply MulEquiv.ext
      intro value
      change
        (F.axioms.unitTransport arrow _ _).transport
          ((F.axioms.unitTransport (𝟙 source.object) _ _).transport.symm
            value) =
          (F.axioms.unitTransport arrow _ _).transport value
      rw [selectedIdentity]
      rfl

namespace BaseArrowLift

variable {F}
variable {source target : FrobenioidIsotropicBase.DStar F}
variable {baseArrow :
  F.preFrobenioid.base.obj source.object ⟶
    F.preFrobenioid.base.obj target.object}

/-- The monoid pullback attached to one Definition 1.3(i)(c) representative.
-/
def pullback (lift : BaseArrowLift F source target baseArrow) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism target.object →*
      F.preFrobenioid.LinearBaseIdentityEndomorphism source.object :=
  (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
      { object := lift.liftedSource
        isotropic := lift.liftedSource_isotropic }
      source lift.sourceBaseIso).toMonoidHom.comp
    (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
      F lift.liftedArrow lift.liftedArrow_linear
        lift.liftedSource_isotropic)

/-- Regard a pullback lift as an object of the carrier slice over its target.
-/
def sliceObject (lift : BaseArrowLift F source target baseArrow) :
    PreFrobenioid.PullbackSliceObject target.object where
  source := lift.liftedSource
  hom := lift.liftedArrow

@[simp]
theorem sliceObject_source
    (lift : BaseArrowLift F source target baseArrow) :
    lift.sliceObject.source = lift.liftedSource :=
  rfl

@[simp]
theorem sliceObject_hom
    (lift : BaseArrowLift F source target baseArrow) :
    lift.sliceObject.hom = lift.liftedArrow :=
  rfl

/-- The base-slice comparison between two representatives of the same base
arrow. -/
def comparisonBaseHom
    (first second : BaseArrowLift F source target baseArrow) :
    F.preFrobenioid.BaseSliceHom
      ((first.sliceObject).toBase F.preFrobenioid)
      ((second.sliceObject).toBase F.preFrobenioid) where
  hom := first.sourceBaseIso.hom ≫ second.sourceBaseIso.inv
  commutes := by
    change
      (first.sourceBaseIso.hom ≫ second.sourceBaseIso.inv) ≫
          F.preFrobenioid.base.map second.liftedArrow =
        F.preFrobenioid.base.map first.liftedArrow
    rw [← second.base_triangle, ← first.base_triangle]
    simp [Category.assoc]

/-- Fullness of Definition 1.3(i)(c) lifts the base comparison to the carrier
slice. -/
def comparisonHom
    (first second : BaseArrowLift F source target baseArrow) :
    PreFrobenioid.PullbackSliceHom
      first.sliceObject second.sliceObject :=
  Classical.choose
    (((F.axioms.pullbackBaseSlices target.object).fullyFaithful
        first.sliceObject second.sliceObject
        first.liftedArrow_pullback second.liftedArrow_pullback).2
      (comparisonBaseHom first second))

theorem comparisonHom_spec
    (first second : BaseArrowLift F source target baseArrow) :
    PreFrobenioid.PullbackSliceHom.toBase F.preFrobenioid
        (comparisonHom first second) =
      comparisonBaseHom first second :=
  Classical.choose_spec
    (((F.axioms.pullbackBaseSlices target.object).fullyFaithful
        first.sliceObject second.sliceObject
        first.liftedArrow_pullback second.liftedArrow_pullback).2
      (comparisonBaseHom first second))

theorem comparisonHom_base
    (first second : BaseArrowLift F source target baseArrow) :
    F.preFrobenioid.base.map (comparisonHom first second).hom =
      first.sourceBaseIso.hom ≫ second.sourceBaseIso.inv := by
  have equality := comparisonHom_spec first second
  rw [PreFrobenioid.BaseSliceHom.mk.injEq] at equality
  exact equality

theorem comparisonHom_linear
    (first second : BaseArrowLift F source target baseArrow) :
    F.preFrobenioid.IsLinear (comparisonHom first second).hom := by
  change F.preFrobenioid.frobeniusDegree
      (comparisonHom first second).hom = 1
  have degrees := congrArg F.preFrobenioid.frobeniusDegree
    (comparisonHom first second).commutes
  rw [F.preFrobenioid.frobeniusDegree_comp] at degrees
  change
    F.preFrobenioid.frobeniusDegree (comparisonHom first second).hom *
        F.preFrobenioid.frobeniusDegree second.liftedArrow =
      F.preFrobenioid.frobeniusDegree first.liftedArrow at degrees
  rw [second.liftedArrow_linear, first.liftedArrow_linear] at degrees
  simpa using degrees

theorem comparisonHom_preStep
    (first second : BaseArrowLift F source target baseArrow) :
    F.preFrobenioid.IsPreStep (comparisonHom first second).hom := by
  refine ⟨comparisonHom_linear first second, ?_⟩
  change IsIso
    (F.preFrobenioid.base.map (comparisonHom first second).hom)
  rw [comparisonHom_base]
  change IsIso
    ((first.sourceBaseIso ≪≫ second.sourceBaseIso.symm).hom)
  infer_instance

theorem comparisonHom_coAngular
    (first second : BaseArrowLift F source target baseArrow) :
    F.preFrobenioid.IsCoAngular (comparisonHom first second).hom :=
  Iut.FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
    F (comparisonHom first second).hom first.liftedSource_isotropic

theorem comparisonBaseIso_trans_sourceBaseIso
    (first second : BaseArrowLift F source target baseArrow) :
    preStepBaseIso F (comparisonHom first second).hom
          (comparisonHom_preStep first second) ≪≫
        second.sourceBaseIso =
      first.sourceBaseIso := by
  apply Iso.ext
  change
    (F.preFrobenioid.base.map (comparisonHom first second).hom) ≫
        second.sourceBaseIso.hom =
      first.sourceBaseIso.hom
  rw [comparisonHom_base]
  calc
    (first.sourceBaseIso.hom ≫ second.sourceBaseIso.inv) ≫
          second.sourceBaseIso.hom =
        first.sourceBaseIso.hom ≫
          (second.sourceBaseIso.inv ≫ second.sourceBaseIso.hom) :=
      Category.assoc _ _ _
    _ = first.sourceBaseIso.hom := by simp

/-- The monoid map is independent of the selected pullback representative.
-/
theorem pullback_eq
    (first second : BaseArrowLift F source target baseArrow) :
    first.pullback = second.pullback := by
  let comparison := comparisonHom first second
  let comparisonPreStep : F.preFrobenioid.IsPreStep comparison.hom :=
    comparisonHom_preStep first second
  let comparisonCoAngular : F.preFrobenioid.IsCoAngular comparison.hom :=
    comparisonHom_coAngular first second
  let comparisonSource : FrobenioidIsotropicBase.DStar F :=
    { object := first.liftedSource
      isotropic := first.liftedSource_isotropic }
  let comparisonTarget : FrobenioidIsotropicBase.DStar F :=
    { object := second.liftedSource
      isotropic := second.liftedSource_isotropic }
  have sourceIsoFactorization :
      Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          comparisonSource source first.sourceBaseIso =
        (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          comparisonSource comparisonTarget
            (preStepBaseIso F comparison.hom comparisonPreStep)).trans
          (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
            comparisonTarget source second.sourceBaseIso) := by
    rw [← comparisonBaseIso_trans_sourceBaseIso first second]
    exact Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv_trans
      F comparisonSource comparisonTarget source
        (preStepBaseIso F comparison.hom comparisonPreStep)
        second.sourceBaseIso
  have pullbackFactorization :
      Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
          F first.liftedArrow first.liftedArrow_linear
            first.liftedSource_isotropic =
        (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
          F comparison.hom (comparisonHom_linear first second)
            first.liftedSource_isotropic).comp
          (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
            F second.liftedArrow second.liftedArrow_linear
              second.liftedSource_isotropic) := by
    have comparisonEquation :
        comparison.hom ≫ second.liftedArrow = first.liftedArrow := by
      simpa [comparison, sliceObject] using
        (comparisonHom first second).commutes
    apply MonoidHom.ext
    intro value
    symm
    apply Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback_unique
      F first.liftedArrow
        first.liftedArrow_linear first.liftedSource_isotropic
    change
      (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback F
        comparison.hom (comparisonHom_linear first second)
          first.liftedSource_isotropic
          (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback F
            second.liftedArrow second.liftedArrow_linear
              second.liftedSource_isotropic value)).hom ≫
          first.liftedArrow =
        first.liftedArrow ≫ value.hom
    let pulledSecond :=
      Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback F
        second.liftedArrow second.liftedArrow_linear
          second.liftedSource_isotropic value
    let pulledComparison :=
      Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback F
        comparison.hom (comparisonHom_linear first second)
          first.liftedSource_isotropic pulledSecond
    calc
      pulledComparison.hom ≫ first.liftedArrow =
          pulledComparison.hom ≫
            (comparison.hom ≫ second.liftedArrow) := by
        exact (congrArg
          (fun arrow => pulledComparison.hom ≫ arrow)
          comparisonEquation).symm
      _ = (pulledComparison.hom ≫ comparison.hom) ≫
            second.liftedArrow := (Category.assoc _ _ _).symm
      _ = (comparison.hom ≫ pulledSecond.hom) ≫
            second.liftedArrow := by
        exact congrArg (fun arrow => arrow ≫ second.liftedArrow)
          (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback_relation
            F comparison.hom (comparisonHom_linear first second)
              first.liftedSource_isotropic pulledSecond)
      _ = comparison.hom ≫
            (pulledSecond.hom ≫ second.liftedArrow) :=
        Category.assoc _ _ _
      _ = comparison.hom ≫
            (second.liftedArrow ≫ value.hom) := by
        exact congrArg (fun arrow => comparison.hom ≫ arrow)
          (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback_relation
            F second.liftedArrow second.liftedArrow_linear
              second.liftedSource_isotropic value)
      _ = (comparison.hom ≫ second.liftedArrow) ≫ value.hom :=
        (Category.assoc _ _ _).symm
      _ = first.liftedArrow ≫ value.hom := by
        exact congrArg (fun arrow => arrow ≫ value.hom) comparisonEquation
  have comparisonPullback := linearEndomorphismPullbackHom_preStep F
    comparison.hom comparisonPreStep comparisonCoAngular
      first.liftedSource_isotropic
  have comparisonTransport := baseIsoRationalMonoidEquiv_preStep F
    comparisonSource comparisonTarget comparison.hom
      comparisonPreStep comparisonCoAngular
  apply MonoidHom.ext
  intro value
  change
    (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
      comparisonSource source first.sourceBaseIso)
        (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
          F first.liftedArrow first.liftedArrow_linear
            first.liftedSource_isotropic value) =
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        comparisonTarget source second.sourceBaseIso)
        (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
          F second.liftedArrow second.liftedArrow_linear
            second.liftedSource_isotropic value)
  rw [sourceIsoFactorization, pullbackFactorization,
    comparisonPullback, comparisonTransport]
  change
    (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
      comparisonTarget source second.sourceBaseIso)
        ((F.axioms.unitTransport comparison.hom comparisonPreStep
          comparisonCoAngular).transport
            ((F.axioms.unitTransport comparison.hom comparisonPreStep
              comparisonCoAngular).transport.symm
                (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
                  F second.liftedArrow second.liftedArrow_linear
                    second.liftedSource_isotropic value))) =
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        comparisonTarget source second.sourceBaseIso)
          (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
            F second.liftedArrow second.liftedArrow_linear
              second.liftedSource_isotropic value)
  rw [MulEquiv.apply_symm_apply]

/-- Reuse the same pullback arrow after changing its source representative by
a base isomorphism. -/
def rebaseSource
    {source' : FrobenioidIsotropicBase.DStar F}
    (lift : BaseArrowLift F source target baseArrow)
    (sourceIso :
      F.preFrobenioid.base.obj source'.object ≅
        F.preFrobenioid.base.obj source.object) :
    BaseArrowLift F source' target (sourceIso.hom ≫ baseArrow) where
  liftedSource := lift.liftedSource
  liftedSource_isotropic := lift.liftedSource_isotropic
  liftedArrow := lift.liftedArrow
  liftedArrow_pullback := lift.liftedArrow_pullback
  liftedArrow_linear := lift.liftedArrow_linear
  liftedArrow_coAngular := lift.liftedArrow_coAngular
  sourceBaseIso := lift.sourceBaseIso ≪≫ sourceIso.symm
  base_triangle := by
    change
      (lift.sourceBaseIso.hom ≫ sourceIso.inv) ≫
          (sourceIso.hom ≫ baseArrow) =
        F.preFrobenioid.base.map lift.liftedArrow
    rw [Category.assoc, Iso.inv_hom_id_assoc, lift.base_triangle]

/-- Rebased source transport is the old transport followed by the inverse
source-isomorphism transport. -/
theorem rebaseSource_pullback
    {source' : FrobenioidIsotropicBase.DStar F}
    (lift : BaseArrowLift F source target baseArrow)
    (sourceIso :
      F.preFrobenioid.base.obj source'.object ≅
        F.preFrobenioid.base.obj source.object) :
    (lift.rebaseSource sourceIso).pullback =
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        source source' sourceIso.symm).toMonoidHom.comp lift.pullback := by
  have transportComposition :=
    Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv_trans F
      { object := lift.liftedSource
        isotropic := lift.liftedSource_isotropic }
      source source' lift.sourceBaseIso sourceIso.symm
  apply MonoidHom.ext
  intro value
  change
    (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
      { object := lift.liftedSource
        isotropic := lift.liftedSource_isotropic }
      source' (lift.sourceBaseIso ≪≫ sourceIso.symm))
        (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
          F lift.liftedArrow lift.liftedArrow_linear
            lift.liftedSource_isotropic value) =
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        source source' sourceIso.symm)
        ((Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          { object := lift.liftedSource
            isotropic := lift.liftedSource_isotropic }
          source lift.sourceBaseIso)
            (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom
              F lift.liftedArrow lift.liftedArrow_linear
                lift.liftedSource_isotropic value))
  rw [transportComposition]
  rfl

variable (source)

/-- Over an identity base arrow, the selected pullback arrow is a co-angular
pre-step. -/
theorem identity_liftedArrow_preStep
    (lift : BaseArrowLift F source source
      (𝟙 (F.preFrobenioid.base.obj source.object))) :
    F.preFrobenioid.IsPreStep lift.liftedArrow := by
  refine ⟨lift.liftedArrow_linear, ?_⟩
  change IsIso (F.preFrobenioid.base.map lift.liftedArrow)
  have mapEquality :
      F.preFrobenioid.base.map lift.liftedArrow =
        lift.sourceBaseIso.hom := by
    simpa using lift.base_triangle.symm
  rw [mapEquality]
  infer_instance

/-- A common co-angular witness computing the source base isomorphism of an
identity-arrow lift. -/
def identityWitness
    (lift : BaseArrowLift F source source
      (𝟙 (F.preFrobenioid.base.obj source.object))) :
    Iut.FrobenioidCoAngularBaseChange.CommonCoAngularPreStepWitness F
      { object := lift.liftedSource
        isotropic := lift.liftedSource_isotropic }
      source lift.sourceBaseIso where
  midpoint := lift.liftedSource
  midpoint_isotropic := lift.liftedSource_isotropic
  toLeft := 𝟙 lift.liftedSource
  toRight := lift.liftedArrow
  toLeft_preStep :=
    Iut.FrobenioidCoAngularBaseChange.isPreStep_of_isIso F
      (𝟙 lift.liftedSource)
  toRight_preStep := identity_liftedArrow_preStep source lift
  toLeft_coAngular :=
    Iut.FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F (𝟙 lift.liftedSource) lift.liftedSource_isotropic
  toRight_coAngular := lift.liftedArrow_coAngular
  leftBaseInverse := 𝟙 _
  leftBaseInverse_hom := by simp
  hom_leftBaseInverse := by simp
  comparison := by
    simpa using lift.base_triangle.symm

/-- The canonical transport along the source isomorphism of an identity lift
is its covariant co-angular unit transport. -/
theorem sourceBaseIso_transport_eq_unitTransport
    (lift : BaseArrowLift F source source
      (𝟙 (F.preFrobenioid.base.obj source.object))) :
    Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        { object := lift.liftedSource
          isotropic := lift.liftedSource_isotropic }
        source lift.sourceBaseIso =
      (F.axioms.unitTransport lift.liftedArrow
        (identity_liftedArrow_preStep source lift)
        lift.liftedArrow_coAngular).transport := by
  let witness := identityWitness source lift
  have selectedIdentity := F.axioms.unitTransport_unique
    (𝟙 lift.liftedSource) witness.toLeft_preStep witness.toLeft_coAngular
    (F.axioms.unitTransport (𝟙 lift.liftedSource)
      witness.toLeft_preStep witness.toLeft_coAngular)
    (Iut.FrobenioidCoAngularBaseChange.identityUnitTransport F
      lift.liftedSource)
  calc
    Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          { object := lift.liftedSource
            isotropic := lift.liftedSource_isotropic }
          source lift.sourceBaseIso = witness.rationalMonoidEquiv :=
      (Iut.FrobenioidCoAngularBaseChange.rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv
        F witness).symm
    _ = (F.axioms.unitTransport lift.liftedArrow
          (identity_liftedArrow_preStep source lift)
          lift.liftedArrow_coAngular).transport := by
      apply MulEquiv.ext
      intro value
      change
        (F.axioms.unitTransport lift.liftedArrow _ _).transport
          ((F.axioms.unitTransport (𝟙 lift.liftedSource) _ _).transport.symm
            value) =
          (F.axioms.unitTransport lift.liftedArrow _ _).transport value
      rw [selectedIdentity]
      rfl

/-- Every Definition 1.3(i)(c) representative over the identity induces the
identity monoid homomorphism. -/
theorem pullback_identity
    (lift : BaseArrowLift F source source
      (𝟙 (F.preFrobenioid.base.obj source.object))) :
    lift.pullback =
      MonoidHom.id
        (F.preFrobenioid.LinearBaseIdentityEndomorphism source.object) := by
  rw [pullback, sourceBaseIso_transport_eq_unitTransport source lift,
    linearEndomorphismPullbackHom_preStep F lift.liftedArrow
      (identity_liftedArrow_preStep source lift)
      lift.liftedArrow_coAngular lift.liftedSource_isotropic]
  apply MonoidHom.ext
  intro value
  simp

end BaseArrowLift

/-- The input for the cartesian square comparing a pullback arrow with a
co-angular pre-step having the same target. -/
structure PullbackPreStepInput
    (left middle target : FrobenioidIsotropicBase.DStar F) where
  pullbackArrow : left.object ⟶ target.object
  pullbackProperty :
    F.preFrobenioid.IsPullback pullbackArrow
  preStepArrow : middle.object ⟶ target.object
  preStepProperty :
    F.preFrobenioid.IsPreStep preStepArrow
  preStepCoAngular :
    F.preFrobenioid.IsCoAngular preStepArrow

namespace PullbackPreStepInput

variable {F}
variable {left middle target : FrobenioidIsotropicBase.DStar F}

theorem pullbackLinear
    (input : PullbackPreStepInput F left middle target) :
    F.preFrobenioid.IsLinear input.pullbackArrow :=
  (F.axioms.pullback_linear_lbInvertible input.pullbackArrow
    input.pullbackProperty).1

/-- The base arrow obtained by pulling the pullback source across the inverse
of the pre-step base isomorphism. -/
def baseArrow (input : PullbackPreStepInput F left middle target) :
    F.preFrobenioid.base.obj left.object ⟶
      F.preFrobenioid.base.obj middle.object :=
  F.preFrobenioid.base.map input.pullbackArrow ≫
    (preStepBaseIso F input.preStepArrow input.preStepProperty).inv

/-- Definition 1.3(i)(c)'s selected pullback lift of the mixed base arrow. -/
def lift (input : PullbackPreStepInput F left middle target) :
    BaseArrowLift F left middle input.baseArrow :=
  baseArrowLift F left middle input.baseArrow

private def comparisonTarget
    (input : PullbackPreStepInput F left middle target) :
    F.preFrobenioid.PullbackComparisonTarget input.pullbackArrow
      input.lift.liftedSource where
  toCodomain := input.lift.liftedArrow ≫ input.preStepArrow
  toBaseDomain := input.lift.sourceBaseIso.hom
  commutes := by
    rw [F.preFrobenioid.base.map_comp, ← input.lift.base_triangle]
    simp [baseArrow, preStepBaseIso, Category.assoc]

/-- The unique carrier arrow completing the pullback/pre-step square. -/
def comparison (input : PullbackPreStepInput F left middle target) :
    input.lift.liftedSource ⟶ left.object :=
  Classical.choose
    ((input.pullbackProperty input.lift.liftedSource).2
      input.comparisonTarget)

theorem comparison_spec
    (input : PullbackPreStepInput F left middle target) :
    F.preFrobenioid.pullbackComparison input.pullbackArrow
        input.lift.liftedSource input.comparison =
      input.comparisonTarget :=
  Classical.choose_spec
    ((input.pullbackProperty input.lift.liftedSource).2
      input.comparisonTarget)

theorem comparison_commutes
    (input : PullbackPreStepInput F left middle target) :
    input.comparison ≫ input.pullbackArrow =
      input.lift.liftedArrow ≫ input.preStepArrow := by
  simpa [PreFrobenioid.pullbackComparison, comparisonTarget] using
    congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
      input.comparison_spec

theorem comparison_base
    (input : PullbackPreStepInput F left middle target) :
    F.preFrobenioid.base.map input.comparison =
      input.lift.sourceBaseIso.hom := by
  simpa [PreFrobenioid.pullbackComparison, comparisonTarget] using
    congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain
      input.comparison_spec

theorem comparison_linear
    (input : PullbackPreStepInput F left middle target) :
    F.preFrobenioid.IsLinear input.comparison := by
  change F.preFrobenioid.frobeniusDegree input.comparison = 1
  have degrees := congrArg F.preFrobenioid.frobeniusDegree
    input.comparison_commutes
  rw [F.preFrobenioid.frobeniusDegree_comp,
    F.preFrobenioid.frobeniusDegree_comp,
    input.pullbackLinear, input.lift.liftedArrow_linear,
    input.preStepProperty.1] at degrees
  simpa using degrees

theorem comparison_preStep
    (input : PullbackPreStepInput F left middle target) :
    F.preFrobenioid.IsPreStep input.comparison := by
  refine ⟨input.comparison_linear, ?_⟩
  change IsIso (F.preFrobenioid.base.map input.comparison)
  rw [input.comparison_base]
  infer_instance

theorem comparison_coAngular
    (input : PullbackPreStepInput F left middle target) :
    F.preFrobenioid.IsCoAngular input.comparison :=
  Iut.FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
    F input.comparison input.lift.liftedSource_isotropic

theorem comparisonBaseIso
    (input : PullbackPreStepInput F left middle target) :
    preStepBaseIso F input.comparison input.comparison_preStep =
      input.lift.sourceBaseIso := by
  apply Iso.ext
  change F.preFrobenioid.base.map input.comparison =
    input.lift.sourceBaseIso.hom
  exact input.comparison_base

/-- Pulling back after covariant transport along the pre-step equals the
transport computed from the cartesian mixed lift. -/
theorem pullback_comp_unitTransport
    (input : PullbackPreStepInput F left middle target) :
    (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
      input.pullbackArrow input.pullbackLinear left.isotropic).comp
        (F.axioms.unitTransport input.preStepArrow
          input.preStepProperty input.preStepCoAngular).transport.toMonoidHom =
      input.lift.pullback := by
  let liftedSource : FrobenioidIsotropicBase.DStar F :=
    { object := input.lift.liftedSource
      isotropic := input.lift.liftedSource_isotropic }
  have comparisonTransport :
      Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          liftedSource left input.lift.sourceBaseIso =
        (F.axioms.unitTransport input.comparison
          input.comparison_preStep input.comparison_coAngular).transport := by
    rw [← input.comparisonBaseIso]
    exact baseIsoRationalMonoidEquiv_preStep F liftedSource left
      input.comparison input.comparison_preStep input.comparison_coAngular
  apply MonoidHom.ext
  intro value
  change
    Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback F
        input.pullbackArrow input.pullbackLinear left.isotropic
          ((F.axioms.unitTransport input.preStepArrow
            input.preStepProperty input.preStepCoAngular).transport value) =
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        liftedSource left input.lift.sourceBaseIso)
          (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback F
            input.lift.liftedArrow input.lift.liftedArrow_linear
              input.lift.liftedSource_isotropic value)
  rw [comparisonTransport]
  let pulled :=
    Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback F
      input.lift.liftedArrow input.lift.liftedArrow_linear
        input.lift.liftedSource_isotropic value
  let transported :=
    (F.axioms.unitTransport input.comparison
      input.comparison_preStep input.comparison_coAngular).transport pulled
  let targetValue :=
    (F.axioms.unitTransport input.preStepArrow
      input.preStepProperty input.preStepCoAngular).transport value
  symm
  apply Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback_unique
    F input.pullbackArrow input.pullbackLinear left.isotropic targetValue
  change transported.hom ≫ input.pullbackArrow =
    input.pullbackArrow ≫ targetValue.hom
  letI : Epi input.comparison :=
    F.carrierTotallyEpimorphic input.comparison
  apply (cancel_epi input.comparison).1
  calc
    input.comparison ≫
          (transported.hom ≫ input.pullbackArrow) =
        (input.comparison ≫ transported.hom) ≫
          input.pullbackArrow :=
      (Category.assoc _ _ _).symm
    _ = (pulled.hom ≫ input.comparison) ≫
          input.pullbackArrow := by
      rw [← (F.axioms.unitTransport input.comparison
        input.comparison_preStep input.comparison_coAngular).conjugates pulled]
    _ = pulled.hom ≫
          (input.comparison ≫ input.pullbackArrow) :=
      Category.assoc _ _ _
    _ = pulled.hom ≫
          (input.lift.liftedArrow ≫ input.preStepArrow) := by
      rw [input.comparison_commutes]
    _ = (pulled.hom ≫ input.lift.liftedArrow) ≫
          input.preStepArrow :=
      (Category.assoc _ _ _).symm
    _ = (input.lift.liftedArrow ≫ value.hom) ≫
          input.preStepArrow := by
      rw [Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullback_relation
        F input.lift.liftedArrow input.lift.liftedArrow_linear
          input.lift.liftedSource_isotropic value]
    _ = input.lift.liftedArrow ≫
          (value.hom ≫ input.preStepArrow) :=
      Category.assoc _ _ _
    _ = input.lift.liftedArrow ≫
          (input.preStepArrow ≫ targetValue.hom) := by
      rw [(F.axioms.unitTransport input.preStepArrow
        input.preStepProperty input.preStepCoAngular).conjugates value]
    _ = (input.lift.liftedArrow ≫ input.preStepArrow) ≫
          targetValue.hom :=
      (Category.assoc _ _ _).symm
    _ = (input.comparison ≫ input.pullbackArrow) ≫
          targetValue.hom := by
      rw [input.comparison_commutes]
    _ = input.comparison ≫
          (input.pullbackArrow ≫ targetValue.hom) :=
      Category.assoc _ _ _

end PullbackPreStepInput

/-- Contravariant rational-monoid transport along a base arrow, computed from
one selected Definition 1.3(i)(c) pullback representative. -/
def baseArrowPullback
    (source target : FrobenioidIsotropicBase.DStar F)
    (baseArrow :
      F.preFrobenioid.base.obj source.object ⟶
        F.preFrobenioid.base.obj target.object) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism target.object →*
      F.preFrobenioid.LinearBaseIdentityEndomorphism source.object :=
  (baseArrowLift F source target baseArrow).pullback

/-- Changing the source of a base arrow by an isomorphism is canceled by the
corresponding covariant base-isomorphism transport. -/
theorem baseArrowPullback_sourceIso
    (source' source target : FrobenioidIsotropicBase.DStar F)
    (sourceIso :
      F.preFrobenioid.base.obj source'.object ≅
        F.preFrobenioid.base.obj source.object)
    (baseArrow :
      F.preFrobenioid.base.obj source.object ⟶
        F.preFrobenioid.base.obj target.object) :
    (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
      source' source sourceIso).toMonoidHom.comp
        (baseArrowPullback F source' target
          (sourceIso.hom ≫ baseArrow)) =
      baseArrowPullback F source target baseArrow := by
  let lift := baseArrowLift F source target baseArrow
  let rebased := lift.rebaseSource sourceIso
  have selectedRepresentative :=
    (baseArrowLift F source' target
      (sourceIso.hom ≫ baseArrow)).pullback_eq rebased
  calc
    (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          source' source sourceIso).toMonoidHom.comp
        (baseArrowPullback F source' target
          (sourceIso.hom ≫ baseArrow)) =
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          source' source sourceIso).toMonoidHom.comp rebased.pullback := by
        rw [baseArrowPullback, selectedRepresentative]
    _ = (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          source' source sourceIso).toMonoidHom.comp
        ((Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          source source' sourceIso.symm).toMonoidHom.comp lift.pullback) := by
      rw [lift.rebaseSource_pullback sourceIso]
    _ = lift.pullback := by
      rw [Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv_symm
        F source' source sourceIso]
      apply MonoidHom.ext
      intro value
      simp
    _ = baseArrowPullback F source target baseArrow := rfl

/-- Pullback transport is compatible with changing its target by a base
isomorphism. -/
theorem baseArrowPullback_targetIso
    (source middle target : FrobenioidIsotropicBase.DStar F)
    (baseArrow :
      F.preFrobenioid.base.obj source.object ⟶
        F.preFrobenioid.base.obj target.object)
    (targetIso :
      F.preFrobenioid.base.obj middle.object ≅
        F.preFrobenioid.base.obj target.object) :
    (baseArrowPullback F source target baseArrow).comp
        (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          middle target targetIso).toMonoidHom =
      baseArrowPullback F source middle
        (baseArrow ≫ targetIso.inv) := by
  let targetLift := baseArrowLift F source target baseArrow
  let targetLiftSource : FrobenioidIsotropicBase.DStar F :=
    { object := targetLift.liftedSource
      isotropic := targetLift.liftedSource_isotropic }
  let witness :=
    Iut.FrobenioidCoAngularBaseChange.commonCoAngularPreSteps F
      middle target targetIso
  let witnessSource : FrobenioidIsotropicBase.DStar F :=
    { object := witness.midpoint
      isotropic := witness.midpoint_isotropic }
  let rightInput : PullbackPreStepInput F
      targetLiftSource witnessSource target :=
    { pullbackArrow := targetLift.liftedArrow
      pullbackProperty := targetLift.liftedArrow_pullback
      preStepArrow := witness.toRight
      preStepProperty := witness.toRight_preStep
      preStepCoAngular := witness.toRight_coAngular }
  let sourceLift := baseArrowLift F source middle
    (baseArrow ≫ targetIso.inv)
  let sourceLiftSource : FrobenioidIsotropicBase.DStar F :=
    { object := sourceLift.liftedSource
      isotropic := sourceLift.liftedSource_isotropic }
  let leftInput : PullbackPreStepInput F
      sourceLiftSource witnessSource middle :=
    { pullbackArrow := sourceLift.liftedArrow
      pullbackProperty := sourceLift.liftedArrow_pullback
      preStepArrow := witness.toLeft
      preStepProperty := witness.toLeft_preStep
      preStepCoAngular := witness.toLeft_coAngular }
  let witnessLeftIso :=
    preStepBaseIso F witness.toLeft witness.toLeft_preStep
  let witnessRightIso :=
    preStepBaseIso F witness.toRight witness.toRight_preStep
  have witnessBaseIso :
      witnessRightIso = witnessLeftIso ≪≫ targetIso := by
    apply Iso.ext
    exact witness.rightBase_eq_leftBase_comp
  have witnessInverseBase :
      targetIso.inv ≫ witnessLeftIso.inv = witnessRightIso.inv := by
    rw [witnessBaseIso]
    rfl
  let commonBaseArrow :
      F.preFrobenioid.base.obj source.object ⟶
        F.preFrobenioid.base.obj witness.midpoint :=
    baseArrow ≫ witnessRightIso.inv
  have rightInputBase :
      rightInput.baseArrow =
        targetLift.sourceBaseIso.hom ≫ commonBaseArrow := by
    calc
      rightInput.baseArrow =
          F.preFrobenioid.base.map targetLift.liftedArrow ≫
            witnessRightIso.inv := rfl
      _ = (targetLift.sourceBaseIso.hom ≫ baseArrow) ≫
            witnessRightIso.inv := by
        rw [targetLift.base_triangle]
      _ = targetLift.sourceBaseIso.hom ≫ commonBaseArrow :=
        Category.assoc _ _ _
  have leftInputBase :
      leftInput.baseArrow =
        sourceLift.sourceBaseIso.hom ≫ commonBaseArrow := by
    calc
      leftInput.baseArrow =
          F.preFrobenioid.base.map sourceLift.liftedArrow ≫
            witnessLeftIso.inv := rfl
      _ = (sourceLift.sourceBaseIso.hom ≫
            (baseArrow ≫ targetIso.inv)) ≫ witnessLeftIso.inv := by
        rw [sourceLift.base_triangle]
      _ = sourceLift.sourceBaseIso.hom ≫
            (baseArrow ≫ (targetIso.inv ≫ witnessLeftIso.inv)) := by
        simp only [Category.assoc]
      _ = sourceLift.sourceBaseIso.hom ≫ commonBaseArrow := by
        rw [witnessInverseBase]
  have rightSourceChange :
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        targetLiftSource source targetLift.sourceBaseIso).toMonoidHom.comp
          rightInput.lift.pullback =
        baseArrowPullback F source witnessSource commonBaseArrow := by
    change
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        targetLiftSource source targetLift.sourceBaseIso).toMonoidHom.comp
          (baseArrowPullback F targetLiftSource witnessSource
            rightInput.baseArrow) =
        baseArrowPullback F source witnessSource commonBaseArrow
    rw [rightInputBase]
    exact baseArrowPullback_sourceIso F targetLiftSource source
      witnessSource targetLift.sourceBaseIso commonBaseArrow
  have leftSourceChange :
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        sourceLiftSource source sourceLift.sourceBaseIso).toMonoidHom.comp
          leftInput.lift.pullback =
        baseArrowPullback F source witnessSource commonBaseArrow := by
    change
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        sourceLiftSource source sourceLift.sourceBaseIso).toMonoidHom.comp
          (baseArrowPullback F sourceLiftSource witnessSource
            leftInput.baseArrow) =
        baseArrowPullback F source witnessSource commonBaseArrow
    rw [leftInputBase]
    exact baseArrowPullback_sourceIso F sourceLiftSource source
      witnessSource sourceLift.sourceBaseIso commonBaseArrow
  have commonSourceEquality :
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        targetLiftSource source targetLift.sourceBaseIso).toMonoidHom.comp
          rightInput.lift.pullback =
        (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          sourceLiftSource source sourceLift.sourceBaseIso).toMonoidHom.comp
            leftInput.lift.pullback := by
    rw [rightSourceChange, leftSourceChange]
  have targetIsoTransport :
      Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          middle target targetIso =
        (F.axioms.unitTransport witness.toLeft witness.toLeft_preStep
          witness.toLeft_coAngular).transport.symm.trans
        (F.axioms.unitTransport witness.toRight witness.toRight_preStep
          witness.toRight_coAngular).transport := by
    rw [← Iut.FrobenioidCoAngularBaseChange.rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv
      F witness]
    rfl
  have rightNaturality := rightInput.pullback_comp_unitTransport
  have leftNaturality := leftInput.pullback_comp_unitTransport
  apply MonoidHom.ext
  intro value
  change
    (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
      targetLiftSource source targetLift.sourceBaseIso)
      (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
        targetLift.liftedArrow targetLift.liftedArrow_linear
          targetLift.liftedSource_isotropic
          (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
            middle target targetIso value)) =
    (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
      sourceLiftSource source sourceLift.sourceBaseIso)
      (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
        sourceLift.liftedArrow sourceLift.liftedArrow_linear
          sourceLift.liftedSource_isotropic value)
  rw [targetIsoTransport]
  let middleValue :=
    (F.axioms.unitTransport witness.toLeft witness.toLeft_preStep
      witness.toLeft_coAngular).transport.symm value
  have rightAt := DFunLike.congr_fun rightNaturality middleValue
  have leftAt := DFunLike.congr_fun leftNaturality middleValue
  have commonAt := DFunLike.congr_fun commonSourceEquality middleValue
  change
    (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
      targetLiftSource source targetLift.sourceBaseIso)
      (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
        targetLift.liftedArrow targetLift.liftedArrow_linear
          targetLift.liftedSource_isotropic
          ((F.axioms.unitTransport witness.toRight witness.toRight_preStep
            witness.toRight_coAngular).transport middleValue)) = _
  calc
    _ = (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          targetLiftSource source targetLift.sourceBaseIso)
        (rightInput.lift.pullback middleValue) := by
      exact congrArg
        (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          targetLiftSource source targetLift.sourceBaseIso) rightAt
    _ = (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          sourceLiftSource source sourceLift.sourceBaseIso)
        (leftInput.lift.pullback middleValue) := commonAt
    _ = (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          sourceLiftSource source sourceLift.sourceBaseIso)
        (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
          sourceLift.liftedArrow sourceLift.liftedArrow_linear
            sourceLift.liftedSource_isotropic value) := by
      apply congrArg
      rw [← leftAt]
      change
        Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
            sourceLift.liftedArrow sourceLift.liftedArrow_linear
              sourceLift.liftedSource_isotropic
              ((F.axioms.unitTransport witness.toLeft witness.toLeft_preStep
                witness.toLeft_coAngular).transport
                ((F.axioms.unitTransport witness.toLeft witness.toLeft_preStep
                  witness.toLeft_coAngular).transport.symm value)) =
          Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
            sourceLift.liftedArrow sourceLift.liftedArrow_linear
              sourceLift.liftedSource_isotropic value
      rw [MulEquiv.apply_symm_apply]

/-- Contravariant base-arrow pullback respects composition. -/
theorem baseArrowPullback_comp
    (source middle target : FrobenioidIsotropicBase.DStar F)
    (firstArrow :
      F.preFrobenioid.base.obj source.object ⟶
        F.preFrobenioid.base.obj middle.object)
    (secondArrow :
      F.preFrobenioid.base.obj middle.object ⟶
        F.preFrobenioid.base.obj target.object) :
    baseArrowPullback F source target (firstArrow ≫ secondArrow) =
      (baseArrowPullback F source middle firstArrow).comp
        (baseArrowPullback F middle target secondArrow) := by
  let secondLift := baseArrowLift F middle target secondArrow
  let secondLiftSource : FrobenioidIsotropicBase.DStar F :=
    { object := secondLift.liftedSource
      isotropic := secondLift.liftedSource_isotropic }
  let adjustedFirstArrow := firstArrow ≫ secondLift.sourceBaseIso.inv
  let firstLift := baseArrowLift F source secondLiftSource adjustedFirstArrow
  let compositeArrow := firstLift.liftedArrow ≫ secondLift.liftedArrow
  have compositePullback :
      F.preFrobenioid.IsPullback compositeArrow :=
    isPullback_comp F firstLift.liftedArrow secondLift.liftedArrow
      firstLift.liftedArrow_pullback secondLift.liftedArrow_pullback
  have compositeProperties :=
    F.axioms.pullback_linear_lbInvertible compositeArrow compositePullback
  let compositeLift : BaseArrowLift F source target
      (firstArrow ≫ secondArrow) :=
    { liftedSource := firstLift.liftedSource
      liftedSource_isotropic := firstLift.liftedSource_isotropic
      liftedArrow := compositeArrow
      liftedArrow_pullback := compositePullback
      liftedArrow_linear := compositeProperties.1
      liftedArrow_coAngular := compositeProperties.2.1
      sourceBaseIso := firstLift.sourceBaseIso
      base_triangle := by
        change
          firstLift.sourceBaseIso.hom ≫
              (firstArrow ≫ secondArrow) =
            F.preFrobenioid.base.map
              (firstLift.liftedArrow ≫ secondLift.liftedArrow)
        rw [F.preFrobenioid.base.map_comp,
          ← firstLift.base_triangle, ← secondLift.base_triangle]
        simp [adjustedFirstArrow, Category.assoc] }
  have selectedComposite :=
    (baseArrowLift F source target
      (firstArrow ≫ secondArrow)).pullback_eq compositeLift
  let secondActualPullback :=
    Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
      secondLift.liftedArrow secondLift.liftedArrow_linear
        secondLift.liftedSource_isotropic
  have actualPullbackComposition :=
    Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom_comp F
      firstLift.liftedArrow secondLift.liftedArrow
        firstLift.liftedArrow_linear secondLift.liftedArrow_linear
          firstLift.liftedSource_isotropic
  have compositeLiftPullback :
      compositeLift.pullback =
        firstLift.pullback.comp secondActualPullback := by
    apply MonoidHom.ext
    intro value
    change
      (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
        { object := firstLift.liftedSource
          isotropic := firstLift.liftedSource_isotropic }
        source firstLift.sourceBaseIso)
          (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
            compositeArrow compositeProperties.1
              firstLift.liftedSource_isotropic value) =
        (Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
          { object := firstLift.liftedSource
            isotropic := firstLift.liftedSource_isotropic }
          source firstLift.sourceBaseIso)
            (Iut.FrobenioidRationalMonoidTransport.linearEndomorphismPullbackHom F
              firstLift.liftedArrow firstLift.liftedArrow_linear
                firstLift.liftedSource_isotropic
                (secondActualPullback value))
    rw [actualPullbackComposition]
    rfl
  have targetCompatibility :=
    baseArrowPullback_targetIso F source secondLiftSource middle
      firstArrow secondLift.sourceBaseIso
  have selectedAt := DFunLike.congr_fun selectedComposite
  have compositeAt := DFunLike.congr_fun compositeLiftPullback
  have targetAt := DFunLike.congr_fun targetCompatibility
  apply MonoidHom.ext
  intro value
  change
    (baseArrowLift F source target
      (firstArrow ≫ secondArrow)).pullback value =
      (baseArrowPullback F source middle firstArrow)
        (secondLift.pullback value)
  calc
    _ = compositeLift.pullback value := selectedAt value
    _ = firstLift.pullback (secondActualPullback value) := compositeAt value
    _ = (baseArrowPullback F source middle firstArrow)
          ((Iut.FrobenioidCoAngularBaseChange.baseIsoRationalMonoidEquiv F
            secondLiftSource middle secondLift.sourceBaseIso)
              (secondActualPullback value)) := by
      exact (targetAt (secondActualPullback value)).symm
    _ = (baseArrowPullback F source middle firstArrow)
          (secondLift.pullback value) := rfl

/-- The selected base-arrow pullback preserves identity arrows. -/
theorem baseArrowPullback_id
    (source : FrobenioidIsotropicBase.DStar F) :
    baseArrowPullback F source source
        (𝟙 (F.preFrobenioid.base.obj source.object)) =
      MonoidHom.id
        (F.preFrobenioid.LinearBaseIdentityEndomorphism source.object) :=
  (baseArrowLift F source source
    (𝟙 (F.preFrobenioid.base.obj source.object))).pullback_identity source

/-- Frobenioids I, Proposition 2.2(ii), packaged on the base-equivalent
category `D*` as the contravariant rational-monoid functor
`O^triangle : (D*)^op -> Mon`. -/
def baseRationalMonoidFunctor :
    (FrobenioidIsotropicBase.DStar F)ᵒᵖ ⥤ MonCat.{u} where
  obj object := MonCat.of
    (F.preFrobenioid.LinearBaseIdentityEndomorphism object.unop.object)
  map {source target} arrow := MonCat.ofHom
    (baseArrowPullback F target.unop source.unop arrow.unop)
  map_id object := by
    apply MonCat.hom_ext
    change
      baseArrowPullback F object.unop object.unop
          (𝟙 (F.preFrobenioid.base.obj object.unop.object)) =
        MonoidHom.id
          (F.preFrobenioid.LinearBaseIdentityEndomorphism
            object.unop.object)
    exact baseArrowPullback_id F object.unop
  map_comp {source middle target} first second := by
    apply MonCat.hom_ext
    change
      baseArrowPullback F target.unop source.unop
          (second.unop ≫ first.unop) =
        (baseArrowPullback F target.unop middle.unop second.unop).comp
          (baseArrowPullback F middle.unop source.unop first.unop)
    exact baseArrowPullback_comp F
      target.unop middle.unop source.unop second.unop first.unop

end

end Iut.FrobenioidBasePullbackLift
