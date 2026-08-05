/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidBirational
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Filtered-colimit birationalization of the model Frobenioid

Frobenioids I, Proposition 4.4 defines `Hom_C^birat(A,B)` as the direct limit
of `Hom_C(A',B)` over co-angular pre-steps `A' → A`.  The transition maps go
from a denominator to each refinement, so the covariant Lean diagram is on
the opposite of the slice indexing category.

This file constructs that indexing category for the model Frobenioid, proves
that its opposite is filtered, forms the actual `Type`-valued colimit, and
proves that the roof map `(α,φ) ↦ α⁻¹φ` is bijective onto the concrete
birational category.  It consequently constructs the colimit-Hom category and
an equivalence with the concrete target.  The Proposition 1.11(vii) refinement
square and Proposition 4.4(i) roof-composition formula are explicit.  The
group-like Frobenioid presentation and complete Proposition 4.4(iv) dictionary
remain separate obligations.
-/

open CategoryTheory CategoryTheory.Limits

namespace Iut.SourceModelFrobenioid

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

namespace Carrier

/-- A co-angular pre-step with fixed codomain, the source index of 4.4. -/
structure CoAngularPreStepOver (target : Carrier Phi data) where
  source : Carrier Phi data
  hom : source ⟶ target
  preStep : (preFrobenioid Phi data).IsPreStep hom
  coAngular : (preFrobenioid Phi data).IsCoAngular hom

namespace CoAngularPreStepOver

@[simp]
theorem birational_comp_frobeniusDegree
    {source middle target : BirationalObject (Phi := Phi) (data := data)}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).frobeniusDegree =
      first.frobeniusDegree * second.frobeniusDegree :=
  rfl

@[simp]
theorem birational_comp_base
    {source middle target : BirationalObject (Phi := Phi) (data := data)}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).base = first.base ≫ second.base :=
  rfl

/-- A refining co-angular pre-step forming a commuting denominator triangle. -/
@[ext]
structure Transition {target : Carrier Phi data}
    (first second : CoAngularPreStepOver target) where
  hom : first.source ⟶ second.source
  preStep : (preFrobenioid Phi data).IsPreStep hom
  coAngular : (preFrobenioid Phi data).IsCoAngular hom
  commutes : hom ≫ second.hom = first.hom

/-- The source slice category restricted to co-angular pre-steps. -/
instance category (target : Carrier Phi data) :
    Category.{u} (CoAngularPreStepOver target) where
  Hom := Transition
  id object :=
    { hom := 𝟙 object.source
      preStep := by
        constructor
        · rfl
        · change IsIso (𝟙 (Object.base object.source))
          infer_instance
      coAngular := isCoAngular Phi data (𝟙 object.source)
      commutes := Category.id_comp object.hom }
  comp first second :=
    { hom := first.hom ≫ second.hom
      preStep := by
        constructor
        · change first.hom.frobeniusDegree * second.hom.frobeniusDegree = 1
          have firstLinear := first.preStep.1
          have secondLinear := second.preStep.1
          change first.hom.frobeniusDegree = 1 at firstLinear
          change second.hom.frobeniusDegree = 1 at secondLinear
          rw [firstLinear, secondLinear]
          rfl
        · have firstBase := first.preStep.2
          have secondBase := second.preStep.2
          change IsIso first.hom.base at firstBase
          change IsIso second.hom.base at secondBase
          change IsIso (first.hom.base ≫ second.hom.base)
          letI : IsIso first.hom.base := firstBase
          letI : IsIso second.hom.base := secondBase
          infer_instance
      coAngular := isCoAngular Phi data (first.hom ≫ second.hom)
      commutes := by
        rw [Category.assoc, second.commutes, first.commutes] }

/-- The identity denominator. -/
def identity (target : Carrier Phi data) : CoAngularPreStepOver target where
  source := target
  hom := 𝟙 target
  preStep := by
    constructor
    · rfl
    · change IsIso (𝟙 (Object.base target))
      infer_instance
  coAngular := isCoAngular Phi data (𝟙 target)

/-- The Hom-set diagram whose transition maps precompose by refinements. -/
def homDiagram (source target : Carrier Phi data) :
    (CoAngularPreStepOver source)ᵒᵖ ⥤ Type u where
  obj index := index.unop.source ⟶ target
  map transition := ↾(fun numerator ↦ transition.unop.hom ≫ numerator)
  map_id _ := by
    ext numerator
    exact Category.id_comp numerator
  map_comp first second := by
    ext numerator
    change (second.unop.hom ≫ first.unop.hom) ≫ numerator =
      second.unop.hom ≫ first.unop.hom ≫ numerator
    exact Category.assoc _ _ _

/-- The concrete isomorphism represented by a denominator. -/
def denominatorIso {target : Carrier Phi data}
    (denominator : CoAngularPreStepOver target) :
    (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).obj
        denominator.source ≅
      (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).obj target := by
  have baseIsIso := denominator.preStep.2
  change IsIso denominator.hom.base at baseIsIso
  exact BirationalObject.isoOfLinearBaseIso
    ((BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
      denominator.hom)
    denominator.preStep.1 baseIsIso

/-- Evaluation of a roof as `denominator⁻¹ ≫ numerator`. -/
def roofValue {source target : Carrier Phi data}
    (denominator : CoAngularPreStepOver source)
    (numerator : denominator.source ⟶ target) :
    (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).obj source ⟶
      (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).obj target :=
  (denominatorIso denominator).inv ≫
    (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map numerator

theorem roofValue_transition
    {source target : Carrier Phi data}
    {first second : CoAngularPreStepOver source}
    (transition : first ⟶ second) (numerator : second.source ⟶ target) :
    roofValue first (transition.hom ≫ numerator) =
      roofValue second numerator := by
  let inclusion := BirationalObject.inclusionFunctor (Phi := Phi) (data := data)
  have transitionBaseIsIso := transition.preStep.2
  change IsIso transition.hom.base at transitionBaseIsIso
  have denominatorBaseIsIso := second.preStep.2
  change IsIso second.hom.base at denominatorBaseIsIso
  letI : IsIso (inclusion.map transition.hom) :=
    (BirationalObject.isoOfLinearBaseIso (inclusion.map transition.hom)
      transition.preStep.1 transitionBaseIsIso).isIso_hom
  letI : IsIso (inclusion.map second.hom) :=
    (denominatorIso second).isIso_hom
  have denominatorEquality := congrArg inclusion.map transition.commutes
  change inclusion.map (transition.hom ≫ second.hom) =
    inclusion.map first.hom at denominatorEquality
  rw [inclusion.map_comp] at denominatorEquality
  have inverseTransition :
      (denominatorIso first).inv ≫ inclusion.map transition.hom =
        (denominatorIso second).inv := by
    apply (cancel_mono (inclusion.map second.hom)).1
    rw [Category.assoc, denominatorEquality]
    change (denominatorIso first).inv ≫ (denominatorIso first).hom =
      (denominatorIso second).inv ≫ (denominatorIso second).hom
    simp
  change (denominatorIso first).inv ≫
      inclusion.map (transition.hom ≫ numerator) =
    (denominatorIso second).inv ≫ inclusion.map numerator
  rw [inclusion.map_comp, ← Category.assoc, inverseTransition]

/-- Cancelling a roof denominator recovers its numerator. -/
@[reassoc]
theorem map_denominator_comp_roofValue
    {source target : Carrier Phi data}
    (denominator : CoAngularPreStepOver source)
    (numerator : denominator.source ⟶ target) :
    (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
          denominator.hom ≫
        roofValue denominator numerator =
      (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
        numerator := by
  change (denominatorIso denominator).hom ≫
      ((denominatorIso denominator).inv ≫
        (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
          numerator) = _
  simp

/-- A roof with identity denominator evaluates to the included numerator. -/
@[simp]
theorem roofValue_identity_denominator
    {source target : Carrier Phi data} (numerator : source ⟶ target) :
    roofValue (identity source) numerator =
      (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
        numerator := by
  have cancellation := map_denominator_comp_roofValue
    (identity source) numerator
  change (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
        (𝟙 source) ≫ roofValue (identity source) numerator = _ at cancellation
  have mappedIdentity :
      (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
          (𝟙 source) = 𝟙 _ :=
    (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map_id
      source
  rw [mappedIdentity, Category.id_comp] at cancellation
  exact cancellation

/-- Roof evaluation as a cocone over the Hom-set diagram. -/
def homCocone (source target : Carrier Phi data) :
    Cocone (homDiagram source target) where
  pt :=
    ((BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).obj source ⟶
      (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).obj target)
  ι :=
    { app index := ↾(fun numerator ↦ roofValue index.unop numerator)
      naturality := by
        intro first second transition
        ext numerator
        exact roofValue_transition transition.unop numerator }

/-- Proposition 4.4's direct-limit Hom type for model objects. -/
abbrev BirationalHomColimit (source target : Carrier Phi data) :=
  colimit (homDiagram source target)

/-- The map from the source colimit to concrete birational arrows. -/
def colimitComparison (source target : Carrier Phi data) :
    BirationalHomColimit source target →
      ((BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).obj source ⟶
        (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).obj target) :=
  fun value ↦ colimit.desc (homDiagram source target) (homCocone source target) value

@[simp]
theorem colimitComparison_ι
    {source target : Carrier Phi data}
    (denominator : CoAngularPreStepOver source)
    (numerator : denominator.source ⟶ target) :
    colimitComparison source target
        (colimit.ι (homDiagram source target) (Opposite.op denominator) numerator) =
      roofValue denominator numerator := by
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (homCocone source target) (Opposite.op denominator)) numerator

/-- A numerator-denominator representative of a concrete arrow's divisor. -/
def liftRepresentative
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (Phi.obj (Object.base source.underlying)).carrier ×
      (⊤ : AddSubmonoid
        (Phi.obj (Object.base source.underlying)).carrier) :=
  Classical.choose (localizationRepresentative arrow.divisorClass)

theorem liftRepresentative_spec
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    arrow.divisorClass =
      AddLocalization.mk (liftRepresentative arrow).1
        (liftRepresentative arrow).2 :=
  Classical.choose_spec (localizationRepresentative arrow.divisorClass)

/-- The effective correction that balances a lifted numerator. -/
def liftCorrection
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (Phi.obj (Object.base source.underlying)).carrier :=
  (liftRepresentative arrow).1 +
    (arrow.frobeniusDegree.val - 1) • (liftRepresentative arrow).2.1

theorem liftCorrection_of
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    Algebra.GrothendieckAddGroup.of (liftCorrection arrow) =
      arrow.divisorClass + arrow.frobeniusDegree.val •
        Algebra.GrothendieckAddGroup.of (liftRepresentative arrow).2.1 := by
  let numerator := (liftRepresentative arrow).1
  let denominator := (liftRepresentative arrow).2
  have fraction := grothendieck_add_denominator
    (Phi.obj (Object.base source.underlying)) numerator denominator
  have representative := liftRepresentative_spec arrow
  have degreeDecomposition :
      arrow.frobeniusDegree.val =
        (arrow.frobeniusDegree.val - 1) + 1 := by
    exact (Nat.sub_add_cancel (PNat.pos arrow.frobeniusDegree)).symm
  have degreeNsmul :
      arrow.frobeniusDegree.val •
          Algebra.GrothendieckAddGroup.of denominator.1 =
        (arrow.frobeniusDegree.val - 1) •
            Algebra.GrothendieckAddGroup.of denominator.1 +
          Algebra.GrothendieckAddGroup.of denominator.1 := by
    calc
      _ = ((arrow.frobeniusDegree.val - 1) + 1) •
          Algebra.GrothendieckAddGroup.of denominator.1 :=
        congrArg (· • Algebra.GrothendieckAddGroup.of denominator.1)
          degreeDecomposition
      _ = _ := by rw [add_nsmul, one_nsmul]
  dsimp only [liftCorrection]
  rw [map_add, map_nsmul]
  change Algebra.GrothendieckAddGroup.of numerator +
      (arrow.frobeniusDegree.val - 1) •
        Algebra.GrothendieckAddGroup.of denominator.1 =
    arrow.divisorClass + arrow.frobeniusDegree.val •
      Algebra.GrothendieckAddGroup.of denominator.1
  rw [representative]
  rw [degreeNsmul]
  rw [← fraction]
  abel

/-- The model object obtained by subtracting the chosen denominator divisor. -/
def liftApex
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) : Carrier Phi data where
  base := Object.base source.underlying
  divisorClass := source.underlying.divisorClass -
    Algebra.GrothendieckAddGroup.of (liftRepresentative arrow).2.1

/-- The pre-step denominator of the roof lifting a concrete arrow. -/
def liftDenominatorHom
    {source target : Carrier Phi data}
    (arrow : BirationalHom ⟨source⟩ ⟨target⟩) :
    liftApex arrow ⟶ source where
  frobeniusDegree := 1
  base := 𝟙 (Object.base source)
  divisor := (liftRepresentative arrow).2.1
  rationalFunction := 0
  balance := by
    change (1 : ℕ) •
          (source.divisorClass -
            Algebra.GrothendieckAddGroup.of
              (liftRepresentative arrow).2.1) +
        Algebra.GrothendieckAddGroup.of (liftRepresentative arrow).2.1 =
      gpPullback Phi (𝟙 (Object.base source)) source.divisorClass +
        data.divisor (Object.base source) 0
    rw [gpPullback_id]
    simp only [AddMonoidHom.id_apply, map_zero, add_zero]
    rw [one_nsmul]
    abel

/-- The lifted denominator as an object of the indexing category. -/
def liftDenominator
    {source target : Carrier Phi data}
    (arrow : BirationalHom ⟨source⟩ ⟨target⟩) :
    CoAngularPreStepOver source where
  source := liftApex arrow
  hom := liftDenominatorHom arrow
  preStep := by
    constructor
    · rfl
    · change IsIso (𝟙 (Object.base source))
      infer_instance
  coAngular := isCoAngular Phi data (liftDenominatorHom arrow)

/-- The balanced model numerator of the roof lifting a concrete arrow. -/
def liftNumerator
    {source target : Carrier Phi data}
    (arrow : BirationalHom ⟨source⟩ ⟨target⟩) :
    liftApex arrow ⟶ target where
  frobeniusDegree := arrow.frobeniusDegree
  base := arrow.base
  divisor := liftCorrection (source := (⟨source⟩ : BirationalObject))
    (target := (⟨target⟩ : BirationalObject)) arrow
  rationalFunction := arrow.rationalFunction
  balance := by
    change arrow.frobeniusDegree.val •
          (source.divisorClass -
            Algebra.GrothendieckAddGroup.of
              (liftRepresentative (source := (⟨source⟩ : BirationalObject))
                (target := (⟨target⟩ : BirationalObject)) arrow).2.1) +
        Algebra.GrothendieckAddGroup.of
          (liftCorrection (source := (⟨source⟩ : BirationalObject))
            (target := (⟨target⟩ : BirationalObject)) arrow) =
      gpPullback Phi arrow.base target.divisorClass +
        data.divisor (Object.base source) arrow.rationalFunction
    rw [liftCorrection_of (source := (⟨source⟩ : BirationalObject))
      (target := (⟨target⟩ : BirationalObject)) arrow]
    simp only [nsmul_sub]
    dsimp [BirationalHom.divisorClass]
    abel

theorem roofValue_lift
    {source target : Carrier Phi data}
    (arrow : BirationalHom ⟨source⟩ ⟨target⟩) :
    roofValue (liftDenominator arrow) (liftNumerator arrow) = arrow := by
  dsimp [roofValue, denominatorIso, BirationalObject.isoOfLinearBaseIso,
    BirationalObject.inverse, liftDenominator, liftDenominatorHom,
    liftNumerator, BirationalObject.inclusionFunctor]
  apply BirationalHom.ext
  · rw [birational_comp_frobeniusDegree]
    simp
  · rw [birational_comp_base]
    simp only [IsIso.inv_comp_eq]
    exact (Category.id_comp arrow.base).symm
  · rw [birational_comp_rationalFunction]
    change data.rationalFunctions.pullback (inv (𝟙 (Object.base source)))
          arrow.rationalFunction + arrow.frobeniusDegree.val •
          (-(data.rationalFunctions.pullback (inv (𝟙 (Object.base source))) 0)) =
      arrow.rationalFunction
    rw [show inv (𝟙 (Object.base source)) = 𝟙 (Object.base source) by simp]
    rw [data.rationalFunctions.pullback_id]
    simp

theorem colimitComparison_surjective (source target : Carrier Phi data) :
    Function.Surjective (colimitComparison source target) := by
  intro arrow
  change BirationalHom ⟨source⟩ ⟨target⟩ at arrow
  refine ⟨colimit.ι (homDiagram source target)
    (Opposite.op (liftDenominator arrow)) (liftNumerator arrow), ?_⟩
  rw [colimitComparison_ι, roofValue_lift]

theorem liftNumerator_isPreStep
    {source target : Carrier Phi data}
    (arrow : BirationalHom ⟨source⟩ ⟨target⟩)
    (linear : arrow.frobeniusDegree = 1)
    (baseIsIso : IsIso arrow.base) :
    (preFrobenioid Phi data).IsPreStep (liftNumerator arrow) := by
  constructor
  · change arrow.frobeniusDegree = 1
    exact linear
  · change IsIso arrow.base
    exact baseIsIso

/-- A common lower denominator and its two transition arrows. -/
structure CommonRefinement {target : Carrier Phi data}
    (first second : CoAngularPreStepOver target) where
  denominator : CoAngularPreStepOver target
  toFirst : denominator ⟶ first
  toSecond : denominator ⟶ second

/-- Common refinement constructed by lifting the quotient of two denominators. -/
def commonRefinement {target : Carrier Phi data}
    (first second : CoAngularPreStepOver target) :
    CommonRefinement first second := by
  let inclusion := BirationalObject.inclusionFunctor (Phi := Phi) (data := data)
  let comparison : BirationalHom ⟨first.source⟩ ⟨second.source⟩ :=
    inclusion.map first.hom ≫ (denominatorIso second).inv
  have comparisonLinear : comparison.frobeniusDegree = 1 := by
    rw [birational_comp_frobeniusDegree]
    have firstLinear := first.preStep.1
    change first.hom.frobeniusDegree = 1 at firstLinear
    change first.hom.frobeniusDegree * 1 = 1
    rw [firstLinear]
    rfl
  have comparisonBaseIsIso : IsIso comparison.base := by
    have firstBaseIsIso := first.preStep.2
    change IsIso first.hom.base at firstBaseIsIso
    have secondBaseIsIso := second.preStep.2
    change IsIso second.hom.base at secondBaseIsIso
    dsimp [comparison]
    change IsIso (first.hom.base ≫ inv second.hom.base)
    letI : IsIso first.hom.base := firstBaseIsIso
    letI : IsIso second.hom.base := secondBaseIsIso
    infer_instance
  let toFirstHom := liftDenominatorHom comparison
  let toSecondHom := liftNumerator comparison
  have toFirstPreStep := (liftDenominator comparison).preStep
  have toSecondPreStep := liftNumerator_isPreStep comparison
    comparisonLinear comparisonBaseIsIso
  have square : toFirstHom ≫ first.hom = toSecondHom ≫ second.hom := by
    letI : inclusion.Faithful :=
      BirationalObject.inclusionFunctor_faithful
        (Phi := Phi) (data := data)
    apply inclusion.map_injective
    simp only [inclusion.map_comp]
    have lifted := roofValue_lift comparison
    change (denominatorIso (liftDenominator comparison)).inv ≫
        inclusion.map toSecondHom = comparison at lifted
    have firstFormula : inclusion.map first.hom =
        ((denominatorIso (liftDenominator comparison)).inv ≫
          inclusion.map toSecondHom) ≫ inclusion.map second.hom := by
      rw [lifted]
      dsimp [comparison]
      change inclusion.map first.hom =
        (inclusion.map first.hom ≫ (denominatorIso second).inv) ≫
          (denominatorIso second).hom
      simp
    rw [firstFormula, Category.assoc]
    change (denominatorIso (liftDenominator comparison)).hom ≫
          (denominatorIso (liftDenominator comparison)).inv ≫
          inclusion.map toSecondHom ≫ inclusion.map second.hom =
      inclusion.map toSecondHom ≫ inclusion.map second.hom
    simp
    rfl
  let denominator : CoAngularPreStepOver target :=
    { source := liftApex comparison
      hom := toFirstHom ≫ first.hom
      preStep := by
        constructor
        · have firstLinear := toFirstPreStep.1
          have secondLinear := first.preStep.1
          change toFirstHom.frobeniusDegree = 1 at firstLinear
          change first.hom.frobeniusDegree = 1 at secondLinear
          change toFirstHom.frobeniusDegree * first.hom.frobeniusDegree = 1
          rw [firstLinear, secondLinear]
          rfl
        · have firstBase := toFirstPreStep.2
          have secondBase := first.preStep.2
          change IsIso toFirstHom.base at firstBase
          change IsIso first.hom.base at secondBase
          change IsIso (toFirstHom.base ≫ first.hom.base)
          letI : IsIso toFirstHom.base := firstBase
          letI : IsIso first.hom.base := secondBase
          infer_instance
      coAngular := isCoAngular Phi data (toFirstHom ≫ first.hom) }
  exact
    { denominator := denominator
      toFirst :=
        { hom := toFirstHom
          preStep := toFirstPreStep
          coAngular := isCoAngular Phi data toFirstHom
          commutes := rfl }
      toSecond :=
        { hom := toSecondHom
          preStep := toSecondPreStep
          coAngular := isCoAngular Phi data toSecondHom
          commutes := square.symm } }

/-- Composition of a denominator with a further co-angular refinement. -/
def composedDenominator {target : Carrier Phi data}
    (denominator : CoAngularPreStepOver target)
    (refinement : CoAngularPreStepOver denominator.source) :
    CoAngularPreStepOver target where
  source := refinement.source
  hom := refinement.hom ≫ denominator.hom
  preStep := by
    constructor
    · have refinementLinear := refinement.preStep.1
      have denominatorLinear := denominator.preStep.1
      change refinement.hom.frobeniusDegree = 1 at refinementLinear
      change denominator.hom.frobeniusDegree = 1 at denominatorLinear
      change refinement.hom.frobeniusDegree *
          denominator.hom.frobeniusDegree = 1
      rw [refinementLinear, denominatorLinear]
      rfl
    · have refinementBase := refinement.preStep.2
      have denominatorBase := denominator.preStep.2
      change IsIso refinement.hom.base at refinementBase
      change IsIso denominator.hom.base at denominatorBase
      change IsIso (refinement.hom.base ≫ denominator.hom.base)
      letI : IsIso refinement.hom.base := refinementBase
      letI : IsIso denominator.hom.base := denominatorBase
      infer_instance
  coAngular := isCoAngular Phi data (refinement.hom ≫ denominator.hom)

/-- The refinement map from a composite denominator to its outer denominator. -/
def composedDenominatorTransition {target : Carrier Phi data}
    (denominator : CoAngularPreStepOver target)
    (refinement : CoAngularPreStepOver denominator.source) :
    composedDenominator denominator refinement ⟶ denominator where
  hom := refinement.hom
  preStep := refinement.preStep
  coAngular := refinement.coAngular
  commutes := rfl

/-- The square used in the source proof of Proposition 4.4(i). -/
structure CompositionSquare
    {source middle : Carrier Phi data}
    (firstDenominator : CoAngularPreStepOver source)
    (firstNumerator : firstDenominator.source ⟶ middle)
    (secondDenominator : CoAngularPreStepOver middle) where
  refinement : CoAngularPreStepOver firstDenominator.source
  across : refinement.source ⟶ secondDenominator.source
  commutes : refinement.hom ≫ firstNumerator =
    across ≫ secondDenominator.hom

/-- The birational quotient lifted to produce the 4.4(i) composition square. -/
def compositionComparison
    {source middle : Carrier Phi data}
    (firstDenominator : CoAngularPreStepOver source)
    (firstNumerator : firstDenominator.source ⟶ middle)
    (secondDenominator : CoAngularPreStepOver middle) :
    BirationalHom ⟨firstDenominator.source⟩ ⟨secondDenominator.source⟩ :=
  (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
      firstNumerator ≫
    (denominatorIso secondDenominator).inv

/-- Proposition 1.11(vii)'s square, constructed in the concrete model. -/
def compositionSquare
    {source middle : Carrier Phi data}
    (firstDenominator : CoAngularPreStepOver source)
    (firstNumerator : firstDenominator.source ⟶ middle)
    (secondDenominator : CoAngularPreStepOver middle) :
    CompositionSquare firstDenominator firstNumerator secondDenominator := by
  let inclusion := BirationalObject.inclusionFunctor (Phi := Phi) (data := data)
  let comparison := compositionComparison firstDenominator firstNumerator
    secondDenominator
  let refinement := liftDenominator comparison
  let across := liftNumerator comparison
  have square : refinement.hom ≫ firstNumerator =
      across ≫ secondDenominator.hom := by
    letI : inclusion.Faithful :=
      BirationalObject.inclusionFunctor_faithful
        (Phi := Phi) (data := data)
    apply inclusion.map_injective
    simp only [inclusion.map_comp]
    have lifted := roofValue_lift comparison
    change (denominatorIso refinement).inv ≫ inclusion.map across =
      comparison at lifted
    have firstFormula : inclusion.map firstNumerator =
        ((denominatorIso refinement).inv ≫ inclusion.map across) ≫
          inclusion.map secondDenominator.hom := by
      rw [lifted]
      dsimp [comparison, compositionComparison]
      change inclusion.map firstNumerator =
        (inclusion.map firstNumerator ≫
            (denominatorIso secondDenominator).inv) ≫
          (denominatorIso secondDenominator).hom
      simp
    rw [firstFormula, Category.assoc]
    change (denominatorIso refinement).hom ≫
          (denominatorIso refinement).inv ≫
          inclusion.map across ≫ inclusion.map secondDenominator.hom =
      inclusion.map across ≫ inclusion.map secondDenominator.hom
    simp
    rfl
  exact
    { refinement := refinement
      across := across
      commutes := square }

/-- The explicit source roof selected for the composite in Proposition 4.4(i). -/
def compositeRoofDenominator
    {source middle : Carrier Phi data}
    (firstDenominator : CoAngularPreStepOver source)
    (firstNumerator : firstDenominator.source ⟶ middle)
    (secondDenominator : CoAngularPreStepOver middle) :
    CoAngularPreStepOver source :=
  composedDenominator firstDenominator
    (compositionSquare firstDenominator firstNumerator secondDenominator).refinement

/-- The source formula `ψ' ∘ φ''` for the numerator of a composite roof. -/
def compositeRoofNumerator
    {source middle target : Carrier Phi data}
    (firstDenominator : CoAngularPreStepOver source)
    (firstNumerator : firstDenominator.source ⟶ middle)
    (secondDenominator : CoAngularPreStepOver middle)
    (secondNumerator : secondDenominator.source ⟶ target) :
    (compositeRoofDenominator firstDenominator firstNumerator
      secondDenominator).source ⟶ target :=
  (compositionSquare firstDenominator firstNumerator
      secondDenominator).across ≫ secondNumerator

/-- Evaluation of the explicit source roof agrees with concrete composition. -/
theorem roofValue_compositeRoof
    {source middle target : Carrier Phi data}
    (firstDenominator : CoAngularPreStepOver source)
    (firstNumerator : firstDenominator.source ⟶ middle)
    (secondDenominator : CoAngularPreStepOver middle)
    (secondNumerator : secondDenominator.source ⟶ target) :
    roofValue
        (compositeRoofDenominator firstDenominator firstNumerator
          secondDenominator)
        (compositeRoofNumerator firstDenominator firstNumerator
          secondDenominator secondNumerator) =
      roofValue firstDenominator firstNumerator ≫
        roofValue secondDenominator secondNumerator := by
  let inclusion := BirationalObject.inclusionFunctor (Phi := Phi) (data := data)
  let square := compositionSquare firstDenominator firstNumerator
    secondDenominator
  let composite := compositeRoofDenominator firstDenominator firstNumerator
    secondDenominator
  letI : IsIso (inclusion.map composite.hom) :=
    (denominatorIso composite).isIso_hom
  apply (cancel_epi (inclusion.map composite.hom)).1
  have mappedSquare := congrArg inclusion.map square.commutes
  simp only [inclusion.map_comp] at mappedSquare
  have compositeMap : inclusion.map composite.hom =
      inclusion.map square.refinement.hom ≫
        inclusion.map firstDenominator.hom := by
    dsimp [composite, compositeRoofDenominator, composedDenominator]
    rw [inclusion.map_comp]
  have mappedSquareAssoc : inclusion.map square.refinement.hom ≫
        inclusion.map firstNumerator ≫
          roofValue secondDenominator secondNumerator =
      inclusion.map square.across ≫
        inclusion.map secondDenominator.hom ≫
          roofValue secondDenominator secondNumerator := by
    simpa only [Category.assoc] using congrArg
      (· ≫ roofValue secondDenominator secondNumerator) mappedSquare
  have reassociateComposite :
      (inclusion.map square.refinement.hom ≫
          inclusion.map firstDenominator.hom) ≫
          (roofValue firstDenominator firstNumerator ≫
            roofValue secondDenominator secondNumerator) =
        inclusion.map square.refinement.hom ≫
          inclusion.map firstDenominator.hom ≫
            roofValue firstDenominator firstNumerator ≫
              roofValue secondDenominator secondNumerator :=
    Category.assoc _ _ _
  have cancelSecondDenominator : inclusion.map square.across ≫
        (inclusion.map secondDenominator.hom ≫
          roofValue secondDenominator secondNumerator) =
      inclusion.map square.across ≫ inclusion.map secondNumerator :=
    congrArg (inclusion.map square.across ≫ ·)
      (map_denominator_comp_roofValue secondDenominator secondNumerator)
  rw [map_denominator_comp_roofValue composite]
  change inclusion.map (square.across ≫ secondNumerator) =
    inclusion.map composite.hom ≫
      (roofValue firstDenominator firstNumerator ≫
        roofValue secondDenominator secondNumerator)
  rw [inclusion.map_comp, compositeMap]
  refine Eq.trans ?_ reassociateComposite.symm
  rw [map_denominator_comp_roofValue_assoc firstDenominator firstNumerator]
  rw [mappedSquareAssoc]
  exact cancelSecondDenominator.symm

/-- The direct-limit indexing category is filtered. -/
instance isFilteredIndexOp (target : Carrier Phi data) :
    IsFiltered (CoAngularPreStepOver target)ᵒᵖ where
  cocone_objs first second := by
    let common := commonRefinement first.unop second.unop
    exact ⟨Opposite.op common.denominator, common.toFirst.op,
      common.toSecond.op, trivial⟩
  cocone_maps {first second} left right := by
    have denominatorMono : Mono first.unop.hom :=
      preStep_mono first.unop.hom first.unop.preStep
    letI : Mono first.unop.hom := denominatorMono
    have unopEquality : left.unop = right.unop := by
      apply Transition.ext
      apply (cancel_mono first.unop.hom).1
      rw [left.unop.commutes, right.unop.commutes]
    have equality : left = right := Quiver.Hom.unop_inj unopEquality
    subst right
    exact ⟨second, 𝟙 second, rfl⟩
  nonempty :=
    ⟨Opposite.op (identity target)⟩

theorem map_transition_numerator_eq
    {source target : Carrier Phi data}
    {first second : CoAngularPreStepOver source}
    (transition : first ⟶ second) (numerator : second.source ⟶ target) :
    (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
        (transition.hom ≫ numerator) =
      (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
          first.hom ≫ roofValue second numerator := by
  let inclusion := BirationalObject.inclusionFunctor (Phi := Phi) (data := data)
  rw [inclusion.map_comp]
  change inclusion.map transition.hom ≫ inclusion.map numerator =
    inclusion.map first.hom ≫
      ((denominatorIso second).inv ≫ inclusion.map numerator)
  have commutes := congrArg inclusion.map transition.commutes
  rw [inclusion.map_comp] at commutes
  rw [← commutes]
  change inclusion.map transition.hom ≫ inclusion.map numerator =
    (inclusion.map transition.hom ≫ (denominatorIso second).hom) ≫
      ((denominatorIso second).inv ≫ inclusion.map numerator)
  simp

theorem colimitComparison_injective (source target : Carrier Phi data) :
    Function.Injective (colimitComparison source target) := by
  intro left right equality
  rcases Limits.Types.jointly_surjective' left with
    ⟨firstIndex, firstNumerator, firstRepresents⟩
  rcases Limits.Types.jointly_surjective' right with
    ⟨secondIndex, secondNumerator, secondRepresents⟩
  rw [← firstRepresents, ← secondRepresents] at equality ⊢
  rw [colimitComparison_ι, colimitComparison_ι] at equality
  let common := commonRefinement firstIndex.unop secondIndex.unop
  apply Limits.Types.colimit_sound'
    (f := common.toFirst.op) (f' := common.toSecond.op)
  change common.toFirst.hom ≫ firstNumerator =
    common.toSecond.hom ≫ secondNumerator
  apply (BirationalObject.inclusionFunctor_faithful
    (Phi := Phi) (data := data)).map_injective
  rw [map_transition_numerator_eq, map_transition_numerator_eq, equality]

/-- The source Hom colimit is equivalent to the concrete roof target. -/
def colimitComparisonEquiv (source target : Carrier Phi data) :
    BirationalHomColimit source target ≃
      BirationalHom ⟨source⟩ ⟨target⟩ :=
  Equiv.ofBijective (colimitComparison source target)
    ⟨colimitComparison_injective source target,
      colimitComparison_surjective source target⟩

@[simp]
theorem colimitComparisonEquiv_iota
    {source target : Carrier Phi data}
    (denominator : CoAngularPreStepOver source)
    (numerator : denominator.source ⟶ target) :
    colimitComparisonEquiv source target
        (colimit.ι (homDiagram source target) (Opposite.op denominator)
          numerator) =
      roofValue denominator numerator :=
  colimitComparison_ι denominator numerator

end CoAngularPreStepOver

/-- Model objects equipped with the filtered-colimit Hom types of 4.4. -/
structure ColimitBirationalObject where
  underlying : Carrier Phi data

namespace ColimitBirationalObject

open CoAngularPreStepOver

/-- Identity transported through the Hom-colimit equivalence. -/
def identity (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    BirationalHomColimit object.underlying object.underlying :=
  (colimitComparisonEquiv object.underlying object.underlying).symm
    (BirationalHom.id ⟨object.underlying⟩)

/-- Composition transported through the Hom-colimit equivalence. -/
def composition
    {source middle target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (first : BirationalHomColimit source.underlying middle.underlying)
    (second : BirationalHomColimit middle.underlying target.underlying) :
    BirationalHomColimit source.underlying target.underlying :=
  (colimitComparisonEquiv source.underlying target.underlying).symm
    (BirationalHom.comp
      (colimitComparisonEquiv source.underlying middle.underlying first)
      (colimitComparisonEquiv middle.underlying target.underlying second))

@[simp]
theorem colimitComparisonEquiv_identity
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    colimitComparisonEquiv object.underlying object.underlying
        (identity object) =
      BirationalHom.id ⟨object.underlying⟩ :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem colimitComparisonEquiv_composition
    {source middle target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (first : BirationalHomColimit source.underlying middle.underlying)
    (second : BirationalHomColimit middle.underlying target.underlying) :
    colimitComparisonEquiv source.underlying target.underlying
        (composition first second) =
      BirationalHom.comp
        (colimitComparisonEquiv source.underlying middle.underlying first)
        (colimitComparisonEquiv middle.underlying target.underlying second) :=
  Equiv.apply_symm_apply _ _

instance category :
    Category.{u} (ColimitBirationalObject (Phi := Phi) (data := data)) where
  Hom source target :=
    BirationalHomColimit source.underlying target.underlying
  id := identity
  comp := composition
  id_comp {source target} arrow := by
    apply (colimitComparisonEquiv _ _).injective
    rw [colimitComparisonEquiv_composition,
      colimitComparisonEquiv_identity]
    change (𝟙 (⟨source.underlying⟩ : BirationalObject) ≫
      colimitComparisonEquiv source.underlying target.underlying arrow) = _
    exact Category.id_comp _
  comp_id {source target} arrow := by
    apply (colimitComparisonEquiv _ _).injective
    rw [colimitComparisonEquiv_composition,
      colimitComparisonEquiv_identity]
    change (colimitComparisonEquiv source.underlying target.underlying arrow ≫
      𝟙 (⟨target.underlying⟩ : BirationalObject)) = _
    exact Category.comp_id _
  assoc {firstObject secondObject thirdObject fourthObject}
      first second third := by
    apply (colimitComparisonEquiv _ _).injective
    rw [colimitComparisonEquiv_composition,
      colimitComparisonEquiv_composition,
      colimitComparisonEquiv_composition,
      colimitComparisonEquiv_composition]
    let f : BirationalHom ⟨firstObject.underlying⟩ ⟨secondObject.underlying⟩ :=
      colimitComparisonEquiv firstObject.underlying secondObject.underlying first
    let g : BirationalHom ⟨secondObject.underlying⟩ ⟨thirdObject.underlying⟩ :=
      colimitComparisonEquiv secondObject.underlying thirdObject.underlying second
    let h : BirationalHom ⟨thirdObject.underlying⟩ ⟨fourthObject.underlying⟩ :=
      colimitComparisonEquiv thirdObject.underlying fourthObject.underlying third
    change BirationalHom.comp (BirationalHom.comp f g) h =
      BirationalHom.comp f (BirationalHom.comp g h)
    exact (birationalCategory (Phi := Phi) (data := data)).assoc f g h

/-- The category composition is the explicit square-and-roof formula of 4.4(i). -/
theorem composition_on_roof_iota
    {source middle target :
      ColimitBirationalObject (Phi := Phi) (data := data)}
    (firstDenominator : CoAngularPreStepOver source.underlying)
    (firstNumerator : firstDenominator.source ⟶ middle.underlying)
    (secondDenominator : CoAngularPreStepOver middle.underlying)
    (secondNumerator : secondDenominator.source ⟶ target.underlying) :
    composition
        (colimit.ι (homDiagram source.underlying middle.underlying)
          (Opposite.op firstDenominator) firstNumerator)
        (colimit.ι (homDiagram middle.underlying target.underlying)
          (Opposite.op secondDenominator) secondNumerator) =
      colimit.ι (homDiagram source.underlying target.underlying)
        (Opposite.op (compositeRoofDenominator firstDenominator
          firstNumerator secondDenominator))
        (compositeRoofNumerator firstDenominator firstNumerator
          secondDenominator secondNumerator) := by
  apply (colimitComparisonEquiv source.underlying target.underlying).injective
  rw [colimitComparisonEquiv_composition]
  simp only [colimitComparisonEquiv_iota]
  exact (roofValue_compositeRoof firstDenominator firstNumerator
    secondDenominator secondNumerator).symm

/-- The canonical functor `C → C^birat` represented by identity denominators. -/
def localizationFunctor :
    Carrier Phi data ⥤ ColimitBirationalObject (Phi := Phi) (data := data) where
  obj object := ⟨object⟩
  map {source target} arrow :=
    colimit.ι (homDiagram source target) (Opposite.op (CoAngularPreStepOver.identity source))
      arrow
  map_id object := by
    apply (colimitComparisonEquiv object object).injective
    change colimitComparisonEquiv object object
        (colimit.ι (homDiagram object object)
          (Opposite.op (CoAngularPreStepOver.identity object)) (𝟙 object)) =
      colimitComparisonEquiv object object (identity ⟨object⟩)
    rw [colimitComparisonEquiv_iota, colimitComparisonEquiv_identity]
    rw [roofValue_identity_denominator]
    exact (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map_id
      object
  map_comp {source middle target} first second := by
    apply (colimitComparisonEquiv source target).injective
    change colimitComparisonEquiv source target
        (colimit.ι (homDiagram source target)
          (Opposite.op (CoAngularPreStepOver.identity source))
          (first ≫ second)) =
      colimitComparisonEquiv source target
        (composition
          (colimit.ι (homDiagram source middle)
            (Opposite.op (CoAngularPreStepOver.identity source)) first)
          (colimit.ι (homDiagram middle target)
            (Opposite.op (CoAngularPreStepOver.identity middle)) second))
    rw [colimitComparisonEquiv_iota, colimitComparisonEquiv_composition]
    simp only [colimitComparisonEquiv_iota, roofValue_identity_denominator]
    exact (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map_comp
      first second

/-- The identity-on-objects comparison to the concrete birational category. -/
def comparisonFunctor :
    ColimitBirationalObject (Phi := Phi) (data := data) ⥤
      BirationalObject (Phi := Phi) (data := data) where
  obj object := ⟨object.underlying⟩
  map {source target} arrow := by
    change BirationalHomColimit source.underlying target.underlying at arrow
    exact colimitComparisonEquiv source.underlying target.underlying arrow
  map_id object := Equiv.apply_symm_apply _ _
  map_comp first second := Equiv.apply_symm_apply _ _

/-- Comparison identifies the colimit localization with the concrete inclusion. -/
@[simp]
theorem comparisonFunctor_map_localizationFunctor
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (comparisonFunctor (Phi := Phi) (data := data)).map
        ((localizationFunctor (Phi := Phi) (data := data)).map arrow) =
      (BirationalObject.inclusionFunctor (Phi := Phi) (data := data)).map
        arrow := by
  change colimitComparisonEquiv source target
      (colimit.ι (homDiagram source target)
        (Opposite.op (CoAngularPreStepOver.identity source)) arrow) = _
  rw [colimitComparisonEquiv_iota, roofValue_identity_denominator]

/-- Proposition 4.4(ii): the canonical localization functor is faithful. -/
theorem localizationFunctor_faithful :
    (localizationFunctor (Phi := Phi) (data := data)).Faithful := by
  constructor
  intro source target first second equality
  apply (BirationalObject.inclusionFunctor_faithful
    (Phi := Phi) (data := data)).map_injective
  rw [← comparisonFunctor_map_localizationFunctor first,
    ← comparisonFunctor_map_localizationFunctor second, equality]

/-- The comparison functor is fully faithful on the proved Hom equivalences. -/
def comparisonFunctor_fullyFaithful :
    (comparisonFunctor (Phi := Phi) (data := data)).FullyFaithful where
  preimage {source target} arrow :=
    by
      change BirationalHom ⟨source.underlying⟩ ⟨target.underlying⟩ at arrow
      exact (colimitComparisonEquiv source.underlying target.underlying).symm arrow
  map_preimage _ := Equiv.apply_symm_apply _ _
  preimage_map _ := Equiv.symm_apply_apply _ _

/-- The identity-on-underlying-objects comparison is essentially surjective. -/
instance comparisonFunctor_essSurj :
    (comparisonFunctor (Phi := Phi) (data := data)).EssSurj where
  mem_essImage target :=
    by
      rcases target with ⟨underlying⟩
      exact ⟨⟨underlying⟩, ⟨Iso.refl _⟩⟩

instance comparisonFunctor_isEquivalence :
    (comparisonFunctor (Phi := Phi) (data := data)).IsEquivalence where
  faithful :=
    (comparisonFunctor_fullyFaithful (Phi := Phi) (data := data)).faithful
  full :=
    (comparisonFunctor_fullyFaithful (Phi := Phi) (data := data)).full
  essSurj := comparisonFunctor_essSurj

/-- Every pre-step is inverted by the canonical birationalization functor. -/
theorem localizationFunctor_map_isIso_of_preStep
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (Carrier.preFrobenioid Phi data).IsPreStep arrow) :
    IsIso ((localizationFunctor (Phi := Phi) (data := data)).map arrow) := by
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  haveI : IsIso (comparison.map
      ((localizationFunctor (Phi := Phi) (data := data)).map arrow)) := by
    rw [comparisonFunctor_map_localizationFunctor]
    exact BirationalObject.inclusion_map_isIso_of_preStep arrow preStep
  exact isIso_of_reflects_iso
    ((localizationFunctor (Phi := Phi) (data := data)).map arrow) comparison

/-- Equivalence between the filtered-colimit and concrete model targets. -/
noncomputable def comparisonEquivalence :
    ColimitBirationalObject (Phi := Phi) (data := data) ≌
      BirationalObject (Phi := Phi) (data := data) :=
  (comparisonFunctor (Phi := Phi) (data := data)).asEquivalence

end ColimitBirationalObject

end Carrier

end


end Iut.SourceModelFrobenioid
