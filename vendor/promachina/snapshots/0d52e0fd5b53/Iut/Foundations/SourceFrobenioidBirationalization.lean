/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidModelType
import Iut.Foundations.SourceFrobenioidRationalMonoidTransport
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Birationalization of an arbitrary Frobenioid

This file contains the presentation-independent part of Frobenioids I,
Proposition 4.4.  Given an arbitrary `FrobenioidPresentation`, its
birationalization is the categorical localization at the co-angular
pre-steps.  The localization maps canonically to the elementary Frobenioid
over the terminal divisorial monoid; this is the square in Proposition 4.4(i).

The right calculus of fractions is kept visible in the first layer below.
For a Frobenioid it is supplied by Proposition 1.11(vii), not by a
model-specific coordinate calculation.
-/

open CategoryTheory

namespace Iut.FrobenioidBirationalization

universe u

noncomputable section

/-- The terminal divisorial additive monoid used in Proposition 4.4(i). -/
@[reducible] def zeroDivisorialAddMonoid : DivisorialAddMonoid where
  carrier := PUnit
  integral _ _ _ _ := Subsingleton.elim _ _
  sharp _ _ := Subsingleton.elim _ _
  saturated value degree hypothesis := by
    refine AddLocalization.induction_on value ?_
    rintro ⟨numerator, denominator⟩
    refine ⟨numerator, ?_⟩
    change (AddLocalization.addMonoidOf _ numerator) =
      AddLocalization.mk numerator denominator
    rw [← AddLocalization.mk_zero_eq_addMonoidOf_mk]
    apply AddLocalization.mk_eq_mk_iff'.2
    exact Subsingleton.elim _ _

/-- The constant terminal divisorial monoid `0_D`. -/
@[reducible] def zeroDivisorialMonoidOn
    (D : Type u) [Category.{u} D]
    (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop) :
    DivisorialMonoidOn D IsFSM where
  obj _ := zeroDivisorialAddMonoid
  pullback _ := 0
  pullback_id _ := by ext value
  pullback_comp _ _ := by ext value
  characteristicallyInjective _ _ _ _ := Subsingleton.elim _ _
  fsmPullbackIsIso _ _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
      fun value ↦ ⟨default, Subsingleton.elim _ _⟩⟩

/-- An arrow of the elementary category attached to the objectwise
Grothendieck groups `Phi^gp`.  This category is kept separate from
`ElementaryFrobenioid`: a nontrivial group is not a sharp divisorial monoid. -/
@[ext]
structure GroupifiedElementaryHom
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : DivisorialMonoidOn D IsFSM) (X Y : D) where
  base : X ⟶ Y
  divisor : Algebra.GrothendieckAddGroup (Phi.obj X).carrier
  frobeniusDegree : ℕ+

namespace GroupifiedElementaryHom

def id
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : DivisorialMonoidOn D IsFSM) (X : D) :
    GroupifiedElementaryHom Phi X X where
  base := 𝟙 X
  divisor := 0
  frobeniusDegree := 1

def comp
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : DivisorialMonoidOn D IsFSM)
    {X Y Z : D} (first : GroupifiedElementaryHom Phi X Y)
    (second : GroupifiedElementaryHom Phi Y Z) :
    GroupifiedElementaryHom Phi X Z where
  base := first.base ≫ second.base
  divisor := Phi.gpPullback first.base second.divisor +
    second.frobeniusDegree.1 • first.divisor
  frobeniusDegree := first.frobeniusDegree * second.frobeniusDegree

end GroupifiedElementaryHom

/-- The elementary category `F_(Phi^gp)` in Proposition 4.4(i). -/
@[ext]
structure GroupifiedElementaryFrobenioid
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (_Phi : DivisorialMonoidOn D IsFSM) where
  base : D

namespace GroupifiedElementaryFrobenioid

instance
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : DivisorialMonoidOn D IsFSM) :
    Category.{u} (GroupifiedElementaryFrobenioid Phi) where
  Hom X Y := GroupifiedElementaryHom Phi X.base Y.base
  id X := GroupifiedElementaryHom.id Phi X.base
  comp first second := GroupifiedElementaryHom.comp Phi first second
  id_comp arrow := by
    ext
    · simp [GroupifiedElementaryHom.comp, GroupifiedElementaryHom.id]
    · change Phi.gpPullback (𝟙 _) arrow.divisor +
          arrow.frobeniusDegree.1 • 0 = arrow.divisor
      rw [Phi.gpPullback_id]
      simp
    · simp [GroupifiedElementaryHom.comp, GroupifiedElementaryHom.id]
  comp_id arrow := by
    ext
    · simp [GroupifiedElementaryHom.comp, GroupifiedElementaryHom.id]
    · change Phi.gpPullback arrow.base 0 + 1 • arrow.divisor =
        arrow.divisor
      rw [map_zero, zero_add, one_nsmul]
    · simp [GroupifiedElementaryHom.comp, GroupifiedElementaryHom.id]
  assoc first second third := by
    ext
    · simp [GroupifiedElementaryHom.comp, Category.assoc]
    · change
        Phi.gpPullback (first.base ≫ second.base) third.divisor +
              third.frobeniusDegree.1 •
                (Phi.gpPullback first.base second.divisor +
                  second.frobeniusDegree.1 • first.divisor) =
            Phi.gpPullback first.base
                (Phi.gpPullback second.base third.divisor +
                  third.frobeniusDegree.1 • second.divisor) +
              (second.frobeniusDegree.1 * third.frobeniusDegree.1) •
                first.divisor
      rw [Phi.gpPullback_comp]
      simp [nsmul_add, mul_nsmul, add_assoc]
    · simp [GroupifiedElementaryHom.comp, mul_assoc]

@[simp]
theorem id_base
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : DivisorialMonoidOn D IsFSM)
    (X : GroupifiedElementaryFrobenioid Phi) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base := rfl

@[simp]
theorem id_divisor
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : DivisorialMonoidOn D IsFSM)
    (X : GroupifiedElementaryFrobenioid Phi) :
    (𝟙 X : X ⟶ X).divisor = 0 := rfl

@[simp]
theorem id_frobeniusDegree
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : DivisorialMonoidOn D IsFSM)
    (X : GroupifiedElementaryFrobenioid Phi) :
    (𝟙 X : X ⟶ X).frobeniusDegree = 1 := rfl

end GroupifiedElementaryFrobenioid

variable (F : FrobenioidPresentation.{u})

private abbrev C := F.carrier
private abbrev D := F.baseCategory
private abbrev P := F.preFrobenioid

/-- The denominators in Proposition 4.4: co-angular pre-steps. -/
def denominators : MorphismProperty F.carrier :=
  fun _ _ arrow ↦ F.preFrobenioid.IsPreStep arrow ∧
    F.preFrobenioid.IsCoAngular arrow

/-- The identity is co-angular in every Frobenioid.  The proof uses exactly
the total-epimorphicity and pre-step monomorphism axioms: in a factorization
of an identity as in Definition 1.2(iii), the middle pre-step is both a split
monomorphism and an epimorphism. -/
theorem isCoAngular_id (X : F.carrier) :
    F.preFrobenioid.IsCoAngular (𝟙 X) := by
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  haveI : Epi gamma := F.carrierTotallyEpimorphic gamma
  have betaRetraction : beta ≫ alpha ≫ gamma = 𝟙 U := by
    apply (cancel_epi gamma).1
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
      congrArg (fun arrow ↦ arrow ≫ gamma) equality
  haveI : Epi beta := F.carrierTotallyEpimorphic beta
  haveI : IsSplitMono beta :=
    IsSplitMono.mk'
      { retraction := alpha ≫ gamma
        id := by simpa only [Category.assoc] using betaRetraction }
  exact isIso_of_epi_of_isSplitMono beta

/-- Co-angular pre-steps contain all identities. -/
theorem denominators_id (X : F.carrier) : denominators F (𝟙 X) := by
  constructor
  · constructor
    · exact F.preFrobenioid.frobeniusDegree_id X
    · change IsIso (F.preFrobenioid.base.map (𝟙 X))
      rw [F.preFrobenioid.base.map_id]
      infer_instance
  · exact isCoAngular_id F X

/-- Co-angular pre-steps are closed under composition. -/
theorem denominators_comp
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (hfirst : denominators F first) (hsecond : denominators F second) :
    denominators F (first ≫ second) := by
  constructor
  · constructor
    · rw [PreFrobenioid.IsLinear,
          F.preFrobenioid.frobeniusDegree_comp,
          hfirst.1.1, hsecond.1.1]
      rfl
    · change IsIso
        (F.preFrobenioid.base.map (first ≫ second))
      rw [F.preFrobenioid.base.map_comp]
      haveI : IsIso (F.preFrobenioid.base.map first) := hfirst.1.2
      haveI : IsIso (F.preFrobenioid.base.map second) := hsecond.1.2
      infer_instance
  · exact F.axioms.coAngular_comp first second hfirst.2 hsecond.2

/-- The identity transport used to expose the coherence forced by Definition
1.3(iii)(c)'s uniqueness clause. -/
def identityUnitTransport (X : F.carrier) :
    F.preFrobenioid.CoAngularUnitTransport (𝟙 X) where
  transport := MulEquiv.refl _
  conjugates alpha := by simp

/-- Unit transport along an identity is the identity equivalence. -/
theorem unitTransport_id (X : F.carrier) :
    (F.axioms.unitTransport (𝟙 X)
      (denominators_id F X).1 (denominators_id F X).2).transport =
      MulEquiv.refl _ := by
  have equality := F.axioms.unitTransport_unique (𝟙 X)
    (denominators_id F X).1 (denominators_id F X).2
    (F.axioms.unitTransport (𝟙 X)
      (denominators_id F X).1 (denominators_id F X).2)
    (identityUnitTransport F X)
  exact congrArg PreFrobenioid.CoAngularUnitTransport.transport equality

/-- Compose the two conjugation equivalences attached to composable
co-angular pre-steps. -/
def compositeUnitTransport
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (firstProperty : denominators F first)
    (secondProperty : denominators F second) :
    F.preFrobenioid.CoAngularUnitTransport (first ≫ second) where
  transport :=
    (F.axioms.unitTransport first firstProperty.1
      firstProperty.2).transport.trans
      (F.axioms.unitTransport second secondProperty.1
        secondProperty.2).transport
  conjugates alpha := by
    let firstTransport := F.axioms.unitTransport first
      firstProperty.1 firstProperty.2
    let secondTransport := F.axioms.unitTransport second
      secondProperty.1 secondProperty.2
    calc
      alpha.hom ≫ (first ≫ second) =
          (alpha.hom ≫ first) ≫ second := by simp
      _ = (first ≫ (firstTransport.transport alpha).hom) ≫
          second := by rw [firstTransport.conjugates]
      _ = first ≫
          ((firstTransport.transport alpha).hom ≫ second) := by simp
      _ = first ≫
          (second ≫
            (secondTransport.transport
              (firstTransport.transport alpha)).hom) := by
        rw [secondTransport.conjugates]
      _ = (first ≫ second) ≫
          (secondTransport.transport
            (firstTransport.transport alpha)).hom := by simp

/-- Unit transport respects composition. -/
theorem unitTransport_comp
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (firstProperty : denominators F first)
    (secondProperty : denominators F second) :
    (F.axioms.unitTransport (first ≫ second)
      (denominators_comp F first second firstProperty secondProperty).1
      (denominators_comp F first second firstProperty secondProperty).2).transport =
      (F.axioms.unitTransport first firstProperty.1
        firstProperty.2).transport.trans
        (F.axioms.unitTransport second secondProperty.1
          secondProperty.2).transport := by
  have equality := F.axioms.unitTransport_unique (first ≫ second)
    (denominators_comp F first second firstProperty secondProperty).1
    (denominators_comp F first second firstProperty secondProperty).2
    (F.axioms.unitTransport (first ≫ second)
      (denominators_comp F first second firstProperty secondProperty).1
      (denominators_comp F first second firstProperty secondProperty).2)
    (compositeUnitTransport F first second firstProperty secondProperty)
  exact congrArg PreFrobenioid.CoAngularUnitTransport.transport equality

/-- A co-angular pre-step over the identity base arrow acts trivially on
linear base-identity endomorphisms. -/
theorem unitTransport_eq_refl_of_baseIdentity
    {X : F.carrier} (arrow : X ⟶ X)
    (property : denominators F arrow)
    (baseIdentity : F.preFrobenioid.IsBaseIdentity arrow) :
    (F.axioms.unitTransport arrow property.1 property.2).transport =
      MulEquiv.refl _ := by
  calc
    (F.axioms.unitTransport arrow property.1 property.2).transport =
        (F.axioms.unitTransport (𝟙 X)
          (denominators_id F X).1 (denominators_id F X).2).transport :=
      F.axioms.unitTransport_dependsOnlyOnBase arrow (𝟙 X)
        property.1 property.2
        (denominators_id F X).1 (denominators_id F X).2
        (by simpa [PreFrobenioid.IsBaseIdentity] using baseIdentity)
    _ = MulEquiv.refl _ := unitTransport_id F X

/-- Consequently a base-identity co-angular pre-step commutes with every
linear base-identity endomorphism at its object. -/
theorem baseIdentity_coAngularPreStep_commutes
    {X : F.carrier} (arrow : X ⟶ X)
    (property : denominators F arrow)
    (baseIdentity : F.preFrobenioid.IsBaseIdentity arrow)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism X) :
    alpha.hom ≫ arrow = arrow ≫ alpha.hom := by
  let transport := F.axioms.unitTransport arrow property.1 property.2
  calc
    alpha.hom ≫ arrow =
        arrow ≫ (transport.transport alpha).hom :=
      transport.conjugates alpha
    _ = arrow ≫ alpha.hom := by
      rw [unitTransport_eq_refl_of_baseIdentity F arrow property
        baseIdentity]
      rfl

/-- Remark 1.3.1: linear base-identity endomorphisms at a source object
commute.  Such an endomorphism is a pre-step and is co-angular because it is
parallel to the identity; Definition 1.3(iii)(c) then makes its conjugation
action trivial. -/
theorem linearBaseIdentityEndomorphism_commutes
    {X : F.carrier}
    (left right : F.preFrobenioid.LinearBaseIdentityEndomorphism X) :
    left.hom ≫ right.hom = right.hom ≫ left.hom := by
  have rightPreStep : F.preFrobenioid.IsPreStep right.hom := by
    refine ⟨right.linear, ?_⟩
    change IsIso (F.preFrobenioid.base.map right.hom)
    rw [right.baseIdentity]
    infer_instance
  have rightCoAngular : F.preFrobenioid.IsCoAngular right.hom :=
    F.axioms.coAngular_parallelToCoAngularPreStep
      (𝟙 X) right.hom (denominators_id F X).1
        (denominators_id F X).2
  exact baseIdentity_coAngularPreStep_commutes F right.hom
    ⟨rightPreStep, rightCoAngular⟩ right.baseIdentity left

/-- Proposition 1.11(vii), in its exact Ore-square form. -/
def HasCoAngularPreStepSquares : Prop :=
  ∀ {A B C : F.carrier}
    (denominator : A ⟶ B), denominators F denominator →
    ∀ numerator : C ⟶ B,
      ∃ (D : F.carrier) (refinement : D ⟶ C),
        denominators F refinement ∧
          ∃ across : D ⟶ A,
            refinement ≫ numerator = across ≫ denominator

/-- The square occurring in Proposition 1.11(vii), packaged so that the
four source factorization cases can be composed without unpacking nested
existentials. -/
structure RightOreSquare
    {A B C : F.carrier} (denominator : A ⟶ B) (numerator : C ⟶ B) where
  source : F.carrier
  refinement : source ⟶ C
  refinement_property : denominators F refinement
  across : source ⟶ A
  commutes : refinement ≫ numerator = across ≫ denominator

namespace RightOreSquare

/-- Paste two right-Ore squares along a factorization of the numerator. -/
def paste
    {A B C E : F.carrier} (denominator : A ⟶ B)
    (first : C ⟶ E) (second : E ⟶ B)
    (outer : RightOreSquare F denominator second)
    (inner : RightOreSquare F outer.refinement first) :
    RightOreSquare F denominator (first ≫ second) where
  source := inner.source
  refinement := inner.refinement
  refinement_property := inner.refinement_property
  across := inner.across ≫ outer.across
  commutes := by
    calc
      inner.refinement ≫ (first ≫ second) =
          (inner.refinement ≫ first) ≫ second :=
        (Category.assoc _ _ _).symm
      _ = (inner.across ≫ outer.refinement) ≫ second := by
        rw [inner.commutes]
      _ = inner.across ≫ (outer.refinement ≫ second) :=
        Category.assoc _ _ _
      _ = inner.across ≫ (outer.across ≫ denominator) := by
        rw [outer.commutes]
      _ = (inner.across ≫ outer.across) ≫ denominator :=
        (Category.assoc _ _ _).symm

end RightOreSquare

/-- A left factor of a pre-step is a pre-step when the right factor is a
pre-step.  This is the pre-step case of Frobenioids I, Proposition 1.7(v). -/
theorem isPreStep_left_of_comp
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (composite : F.preFrobenioid.IsPreStep (first ≫ second))
    (right : F.preFrobenioid.IsPreStep second) :
    F.preFrobenioid.IsPreStep first := by
  constructor
  · have compositeLinear := composite.1
    rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      right.1] at compositeLinear
    simpa using compositeLinear
  · change IsIso (F.preFrobenioid.base.map first)
    haveI : IsIso (F.preFrobenioid.base.map second) := right.2
    haveI : IsIso
        (F.preFrobenioid.base.map first ≫
          F.preFrobenioid.base.map second) := by
      rw [← F.preFrobenioid.base.map_comp]
      exact composite.2
    exact IsIso.of_isIso_comp_right
      (F.preFrobenioid.base.map first)
      (F.preFrobenioid.base.map second)

/-- Co-angularity of a composite with a right pre-step forces
co-angularity of the left factor.  The proof is the defining co-angular
test with the right pre-step appended to the final linear factor. -/
theorem isCoAngular_left_of_comp_preStep
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (composite : F.preFrobenioid.IsCoAngular (first ≫ second))
    (right : F.preFrobenioid.IsPreStep second) :
    F.preFrobenioid.IsCoAngular first := by
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  apply composite gamma beta (alpha ≫ second)
  · simpa only [Category.assoc] using congrArg (fun arrow ↦ arrow ≫ second) equality
  · rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      alphaLinear, right.1]
    rfl
  · exact betaPreStep
  · exact betaIsometric
  · rcases baseAlternative with alphaBaseIso | gammaBaseIso
    · left
      change IsIso (F.preFrobenioid.base.map (alpha ≫ second))
      rw [F.preFrobenioid.base.map_comp]
      haveI : IsIso (F.preFrobenioid.base.map alpha) := alphaBaseIso
      haveI : IsIso (F.preFrobenioid.base.map second) := right.2
      infer_instance
    · exact Or.inr gammaBaseIso

/-- Co-angularity of a composite reflects to its right factor when the left
factor has invertible base.  The left factor is absorbed into the first test
arrow in Definition 1.2(ii). -/
theorem isCoAngular_right_of_comp_baseIso
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (firstBaseIso : F.preFrobenioid.IsBaseIso first)
    (composite : F.preFrobenioid.IsCoAngular (first ≫ second)) :
    F.preFrobenioid.IsCoAngular second := by
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  apply composite (first ≫ gamma) beta alpha
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
      haveI : IsIso (F.preFrobenioid.base.map first) := firstBaseIso
      haveI : IsIso (F.preFrobenioid.base.map gamma) := gammaBaseIso
      infer_instance

/-- A base-isomorphism left factor of a co-angular composite is co-angular
when the right factor is linear.  If the final factor in a co-angular test is
a base isomorphism, total invertibility of the displayed base composite forces
the initial factor to be a base isomorphism as well. -/
theorem isCoAngular_left_of_comp_linear
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (firstBaseIso : F.preFrobenioid.IsBaseIso first)
    (secondLinear : F.preFrobenioid.IsLinear second)
    (composite : F.preFrobenioid.IsCoAngular (first ≫ second)) :
    F.preFrobenioid.IsCoAngular first := by
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  have gammaBaseIso : F.preFrobenioid.IsBaseIso gamma := by
    rcases baseAlternative with alphaBaseIso | gammaBaseIso
    · change IsIso (F.preFrobenioid.base.map gamma)
      haveI : IsIso (F.preFrobenioid.base.map first) := firstBaseIso
      haveI : IsIso (F.preFrobenioid.base.map beta) := betaPreStep.2
      haveI : IsIso (F.preFrobenioid.base.map alpha) := alphaBaseIso
      haveI : IsIso
          (F.preFrobenioid.base.map ((gamma ≫ beta) ≫ alpha)) := by
        rw [Category.assoc, equality]
        infer_instance
      haveI : IsIso
          (F.preFrobenioid.base.map (gamma ≫ beta) ≫
            F.preFrobenioid.base.map alpha) := by
        rw [← F.preFrobenioid.base.map_comp]
        infer_instance
      haveI : IsIso (F.preFrobenioid.base.map (gamma ≫ beta)) :=
        IsIso.of_isIso_comp_right _
          (F.preFrobenioid.base.map alpha)
      haveI : IsIso
          (F.preFrobenioid.base.map gamma ≫
            F.preFrobenioid.base.map beta) := by
        rw [← F.preFrobenioid.base.map_comp]
        infer_instance
      exact IsIso.of_isIso_comp_right
        (F.preFrobenioid.base.map gamma)
        (F.preFrobenioid.base.map beta)
    · exact gammaBaseIso
  apply composite gamma beta (alpha ≫ second)
  · simpa only [Category.assoc] using congrArg (fun arrow ↦ arrow ≫ second) equality
  · rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      alphaLinear, secondLinear]
    rfl
  · exact betaPreStep
  · exact betaIsometric
  · exact Or.inr gammaBaseIso

/-- If a composite and its right factor are co-angular pre-steps, then so
is its left factor. -/
theorem denominators_left_of_comp
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (composite : denominators F (first ≫ second))
    (right : denominators F second) :
    denominators F first :=
  ⟨isPreStep_left_of_comp F first second composite.1 right.1,
    isCoAngular_left_of_comp_preStep F first second composite.2 right.1⟩

/-- Pre-steps are closed under composition. -/
theorem isPreStep_comp
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (left : F.preFrobenioid.IsPreStep first)
    (right : F.preFrobenioid.IsPreStep second) :
    F.preFrobenioid.IsPreStep (first ≫ second) := by
  constructor
  · rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      left.1, right.1]
    rfl
  · change IsIso (F.preFrobenioid.base.map (first ≫ second))
    rw [F.preFrobenioid.base.map_comp]
    haveI : IsIso (F.preFrobenioid.base.map first) := left.2
    haveI : IsIso (F.preFrobenioid.base.map second) := right.2
    infer_instance

/-- Remark 1.2.1: a pull-back morphism over a base isomorphism is an
isomorphism. -/
theorem isIso_of_pullback_baseIso
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (pullback : F.preFrobenioid.IsPullback arrow)
    (baseIso : F.preFrobenioid.IsBaseIso arrow) : IsIso arrow := by
  haveI : IsIso (F.preFrobenioid.base.map arrow) := baseIso
  let inverseTarget :
      F.preFrobenioid.PullbackComparisonTarget arrow Y :=
    { toCodomain := 𝟙 Y
      toBaseDomain := inv (F.preFrobenioid.base.map arrow)
      commutes := by simp }
  let inverseExistence := (pullback Y).2 inverseTarget
  let inverse := Classical.choose inverseExistence
  have inverseComparison := Classical.choose_spec inverseExistence
  have inverse_hom : inverse ≫ arrow = 𝟙 Y := by
    exact congrArg (fun value ↦ value.toCodomain) inverseComparison
  haveI : Epi inverse := F.carrierTotallyEpimorphic inverse
  have hom_inverse : arrow ≫ inverse = 𝟙 X := by
    apply (cancel_epi inverse).1
    rw [← Category.assoc, inverse_hom, Category.comp_id,
      Category.id_comp]
  exact IsIso.mk ⟨inverse, hom_inverse, inverse_hom⟩

/-- Every isomorphism in the carrier is a pre-step. -/
theorem isPreStep_of_isIso
    {X Y : F.carrier} (arrow : X ⟶ Y) [IsIso arrow] :
    F.preFrobenioid.IsPreStep arrow := by
  constructor
  · rw [PreFrobenioid.IsLinear]
    have degreeEquation := F.preFrobenioid.frobeniusDegree_comp
      arrow (inv arrow)
    rw [IsIso.hom_inv_id, F.preFrobenioid.frobeniusDegree_id] at degreeEquation
    apply Subtype.ext
    have valueEquation := congrArg Subtype.val degreeEquation
    change 1 =
      (F.preFrobenioid.frobeniusDegree arrow).1 *
        (F.preFrobenioid.frobeniusDegree (inv arrow)).1 at valueEquation
    exact (mul_eq_one.mp valueEquation.symm).1
  · change IsIso (F.preFrobenioid.base.map arrow)
    infer_instance

/-- Every isomorphism is co-angular. -/
theorem isCoAngular_of_isIso
    {X Y : F.carrier} (arrow : X ⟶ Y) [IsIso arrow] :
    F.preFrobenioid.IsCoAngular arrow := by
  have inversePreStep := isPreStep_of_isIso F (inv arrow)
  have compositeCoAngular :
      F.preFrobenioid.IsCoAngular (arrow ≫ inv arrow) := by
    rw [IsIso.hom_inv_id]
    exact isCoAngular_id F X
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  exact isCoAngular_left_of_comp_preStep F arrow (inv arrow)
    compositeCoAngular inversePreStep gamma beta alpha equality
      alphaLinear betaPreStep betaIsometric baseAlternative

/-- Every source isomorphism is isometric.  The divisor equation for the
composite with its inverse writes the arrow's divisor as an additive unit;
sharpness forces it to vanish. -/
theorem isIsometric_of_isIso
    {X Y : F.carrier} (arrow : X ⟶ Y) [IsIso arrow] :
    F.preFrobenioid.IsIsometric arrow := by
  have inversePreStep := isPreStep_of_isIso F (inv arrow)
  have projected := congrArg F.preFrobenioid.divisor
    (IsIso.hom_inv_id arrow)
  rw [F.preFrobenioid.divisor_comp,
    F.preFrobenioid.divisor_id, inversePreStep.1] at projected
  change F.preFrobenioid.divisorMonoid.pullback
      (F.preFrobenioid.base.map arrow)
        (F.preFrobenioid.divisor (inv arrow)) +
      (1 : ℕ) • F.preFrobenioid.divisor arrow = 0 at projected
  rw [one_nsmul] at projected
  apply (F.preFrobenioid.divisorMonoid.obj
    (F.preFrobenioid.base.obj X)).sharp
  rw [isAddUnit_iff_exists]
  refine ⟨F.preFrobenioid.divisorMonoid.pullback
    (F.preFrobenioid.base.map arrow)
      (F.preFrobenioid.divisor (inv arrow)), ?_, projected⟩
  simpa only [add_comm] using projected

/-- The pre-step in a Definition 1.3(iv) factorization of a co-angular
morphism is co-angular when the final pull-back factor is an isomorphism. -/
theorem factorization_preStep_coAngular
    {X Y : F.carrier} {arrow : X ⟶ Y}
    (factorization : F.preFrobenioid.FrobenioidFactorization arrow)
    (arrowCoAngular : F.preFrobenioid.IsCoAngular arrow)
    (pullbackIso : IsIso factorization.pullback) :
    F.preFrobenioid.IsCoAngular factorization.preStep := by
  haveI : IsIso factorization.pullback := pullbackIso
  have pullbackPreStep := isPreStep_of_isIso F factorization.pullback
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  apply arrowCoAngular (factorization.frobenius ≫ gamma) beta
    (alpha ≫ factorization.pullback)
  · have middleEquality := congrArg
      (fun middle ↦ factorization.frobenius ≫ middle ≫
        factorization.pullback) equality
    simpa only [Category.assoc] using
      middleEquality.trans factorization.composite
  · rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      alphaLinear, pullbackPreStep.1]
    rfl
  · exact betaPreStep
  · exact betaIsometric
  · rcases baseAlternative with alphaBaseIso | gammaBaseIso
    · left
      change IsIso
        (F.preFrobenioid.base.map (alpha ≫ factorization.pullback))
      rw [F.preFrobenioid.base.map_comp]
      haveI : IsIso (F.preFrobenioid.base.map alpha) := alphaBaseIso
      infer_instance
    · right
      change IsIso
        (F.preFrobenioid.base.map
          (factorization.frobenius ≫ gamma))
      rw [F.preFrobenioid.base.map_comp]
      haveI : IsIso
          (F.preFrobenioid.base.map factorization.frobenius) :=
        factorization.frobenius_type.2
      haveI : IsIso (F.preFrobenioid.base.map gamma) := gammaBaseIso
      infer_instance

/-- Proposition 1.11(vii) when both arrows into the common codomain are
co-angular pre-steps.  The common source represents the sum of their two
incoming divisors; Definition 1.3(iii)(d) supplies the two comparison maps. -/
def rightOreSquare_coAngularPreStep
    {A B C : F.carrier} (denominator : A ⟶ B) (numerator : C ⟶ B)
    (denominatorProperty : denominators F denominator)
    (numeratorProperty : denominators F numerator) :
    RightOreSquare F denominator numerator := by
  let denominatorDivisorExistence :=
    F.axioms.incomingDivisor denominator denominatorProperty.1
      denominatorProperty.2
  let denominatorDivisor := Classical.choose denominatorDivisorExistence
  have denominatorDivisorEquation :=
    (Classical.choose_spec denominatorDivisorExistence).1
  let numeratorDivisorExistence :=
    F.axioms.incomingDivisor numerator numeratorProperty.1
      numeratorProperty.2
  let numeratorDivisor := Classical.choose numeratorDivisorExistence
  have numeratorDivisorEquation :=
    (Classical.choose_spec numeratorDivisorExistence).1
  let denominatorIncoming :
      F.preFrobenioid.IncomingCoAngularPreStep B denominatorDivisor :=
    { source := A
      hom := denominator
      preStep := denominatorProperty.1
      coAngular := denominatorProperty.2
      pulledBack_divisor_eq := denominatorDivisorEquation }
  let numeratorIncoming :
      F.preFrobenioid.IncomingCoAngularPreStep B numeratorDivisor :=
    { source := C
      hom := numerator
      preStep := numeratorProperty.1
      coAngular := numeratorProperty.2
      pulledBack_divisor_eq := numeratorDivisorEquation }
  let common := F.axioms.incomingDivisorRepresentative B
    (denominatorDivisor + numeratorDivisor)
  have denominatorLe :
      denominatorDivisor ≤ denominatorDivisor + numeratorDivisor :=
    ⟨numeratorDivisor, rfl⟩
  have numeratorLe :
      numeratorDivisor ≤ denominatorDivisor + numeratorDivisor :=
    ⟨denominatorDivisor, add_comm _ _⟩
  let toDenominatorExistence :=
    (F.axioms.incomingDivisorOrderFullyFaithful common
      denominatorIncoming).1 denominatorLe
  let toDenominator := Classical.choose toDenominatorExistence
  have toDenominatorCommutes :=
    (Classical.choose_spec toDenominatorExistence).1
  let toNumeratorExistence :=
    (F.axioms.incomingDivisorOrderFullyFaithful common
      numeratorIncoming).1 numeratorLe
  let toNumerator := Classical.choose toNumeratorExistence
  have toNumeratorCommutes :=
    (Classical.choose_spec toNumeratorExistence).1
  have toNumeratorComposite : denominators F (toNumerator ≫ numerator) := by
    rw [toNumeratorCommutes]
    exact ⟨common.preStep, common.coAngular⟩
  exact
    { source := common.source
      refinement := toNumerator
      refinement_property := denominators_left_of_comp F
        toNumerator numerator toNumeratorComposite numeratorProperty
      across := toDenominator
      commutes := toNumeratorCommutes.trans toDenominatorCommutes.symm }

/-- Proposition 1.11(vii) for an isometric pre-step numerator.  Pull the
denominator's incoming divisor across the base isomorphism, represent it by a
co-angular pre-step, factor the resulting composite isometric-then-co-angular,
and identify its co-angular factor by Definition 1.3(iii)(d).  This is the
construction used in the proof of Proposition 1.9(ii). -/
def rightOreSquare_isometricPreStep
    {A B C : F.carrier} (denominator : A ⟶ B) (numerator : C ⟶ B)
    (denominatorProperty : denominators F denominator)
    (numeratorPreStep : F.preFrobenioid.IsPreStep numerator)
    (numeratorIsometric : F.preFrobenioid.IsIsometric numerator) :
    RightOreSquare F denominator numerator := by
  let denominatorDivisorExistence :=
    F.axioms.incomingDivisor denominator denominatorProperty.1
      denominatorProperty.2
  let denominatorDivisor := Classical.choose denominatorDivisorExistence
  have denominatorDivisorEquation :=
    (Classical.choose_spec denominatorDivisorExistence).1
  let denominatorIncoming :
      F.preFrobenioid.IncomingCoAngularPreStep B denominatorDivisor :=
    { source := A
      hom := denominator
      preStep := denominatorProperty.1
      coAngular := denominatorProperty.2
      pulledBack_divisor_eq := denominatorDivisorEquation }
  let pulledDivisor := F.preFrobenioid.divisorMonoid.pullback
    (F.preFrobenioid.base.map numerator) denominatorDivisor
  let refinementRepresentative :=
    F.axioms.incomingDivisorRepresentative C pulledDivisor
  have compositePreStep := isPreStep_comp F
    refinementRepresentative.hom numerator
    refinementRepresentative.preStep numeratorPreStep
  let factorizationExistence :=
    F.axioms.preStep_isometricThenCoAngular
      (refinementRepresentative.hom ≫ numerator) compositePreStep
  let factorization := Classical.choice factorizationExistence
  have firstIsometric :
      F.preFrobenioid.IsIsometric factorization.first := by
    exact factorization.first_kind
  have secondCoAngular :
      F.preFrobenioid.IsCoAngular factorization.second := by
    exact factorization.second_kind
  have compositeIncomingEquation :
      F.preFrobenioid.divisorMonoid.pullback
          (F.preFrobenioid.base.map
            (refinementRepresentative.hom ≫ numerator))
          denominatorDivisor =
        F.preFrobenioid.divisor
          (refinementRepresentative.hom ≫ numerator) := by
    rw [F.preFrobenioid.base.map_comp,
      F.preFrobenioid.divisorMonoid.pullback_comp,
      F.preFrobenioid.divisor_comp,
      numeratorIsometric, numeratorPreStep.1]
    change
      F.preFrobenioid.divisorMonoid.pullback
          (F.preFrobenioid.base.map refinementRepresentative.hom)
          pulledDivisor =
        F.preFrobenioid.divisorMonoid.pullback
            (F.preFrobenioid.base.map refinementRepresentative.hom) 0 +
          1 • F.preFrobenioid.divisor refinementRepresentative.hom
    rw [refinementRepresentative.pulledBack_divisor_eq]
    rw [map_zero, zero_add, one_nsmul]
  have factorizationIncomingEquation :
      F.preFrobenioid.divisorMonoid.pullback
          (F.preFrobenioid.base.map
            (factorization.first ≫ factorization.second))
          denominatorDivisor =
        F.preFrobenioid.divisor
          (factorization.first ≫ factorization.second) := by
    rw [factorization.composite]
    exact compositeIncomingEquation
  have secondIncomingEquation :
      F.preFrobenioid.divisorMonoid.pullback
          (F.preFrobenioid.base.map factorization.second)
          denominatorDivisor =
        F.preFrobenioid.divisor factorization.second := by
    apply F.preFrobenioid.divisorMonoid.characteristicallyInjective
      (F.preFrobenioid.base.map factorization.first)
    have equation := factorizationIncomingEquation
    rw [F.preFrobenioid.base.map_comp,
      F.preFrobenioid.divisorMonoid.pullback_comp,
      F.preFrobenioid.divisor_comp,
      factorization.second_preStep.1, firstIsometric] at equation
    simpa using equation
  let factorizationIncoming :
      F.preFrobenioid.IncomingCoAngularPreStep B denominatorDivisor :=
    { source := factorization.midpoint
      hom := factorization.second
      preStep := factorization.second_preStep
      coAngular := secondCoAngular
      pulledBack_divisor_eq := secondIncomingEquation }
  let comparisonExistence :=
    F.axioms.incomingDivisorRepresentative_unique
      factorizationIncoming denominatorIncoming
  let comparison := Classical.choose comparisonExistence
  have comparisonCommutes :=
    (Classical.choose_spec comparisonExistence).1
  exact
    { source := refinementRepresentative.source
      refinement := refinementRepresentative.hom
      refinement_property :=
        ⟨refinementRepresentative.preStep,
          refinementRepresentative.coAngular⟩
      across := factorization.first ≫ comparison.hom
      commutes := by
        calc
          refinementRepresentative.hom ≫ numerator =
              factorization.first ≫ factorization.second :=
            factorization.composite.symm
          _ = factorization.first ≫
              (comparison.hom ≫ denominator) :=
            congrArg (fun arrow ↦ factorization.first ≫ arrow)
              comparisonCommutes.symm
          _ = (factorization.first ≫ comparison.hom) ≫ denominator :=
            (Category.assoc _ _ _).symm }

/-- Proposition 1.11(vii) for a pull-back numerator.  Definition 1.3(i)(c)
lifts the required base arrow to a pull-back arrow over the denominator's
domain; the representable universal property of the numerator then produces
the square. -/
def rightOreSquare_pullback
    {A B C : F.carrier} (denominator : A ⟶ B) (numerator : C ⟶ B)
    (denominatorProperty : denominators F denominator)
    (numeratorPullback : F.preFrobenioid.IsPullback numerator) :
    RightOreSquare F denominator numerator := by
  haveI : IsIso (F.preFrobenioid.base.map denominator) :=
    denominatorProperty.1.2
  let baseTarget : F.preFrobenioid.BaseSliceObject A :=
    { source := F.preFrobenioid.base.obj C
      hom := F.preFrobenioid.base.map numerator ≫
        inv (F.preFrobenioid.base.map denominator) }
  let liftedExistence :=
    (F.axioms.pullbackBaseSlices A).essentiallySurjective baseTarget
  let lifted := Classical.choose liftedExistence
  have liftedPullback := (Classical.choose_spec liftedExistence).1
  let baseComparison := Classical.choice
    (Classical.choose_spec liftedExistence).2
  have baseComparisonCommutes := baseComparison.hom_commutes
  change baseComparison.iso.hom ≫ baseTarget.hom =
    F.preFrobenioid.base.map lifted.hom at baseComparisonCommutes
  let comparisonTarget :
      F.preFrobenioid.PullbackComparisonTarget numerator lifted.source :=
    { toCodomain := lifted.hom ≫ denominator
      toBaseDomain := baseComparison.iso.hom
      commutes := by
        rw [F.preFrobenioid.base.map_comp,
          ← baseComparisonCommutes]
        dsimp [baseTarget]
        calc
          (baseComparison.iso.hom ≫
                (F.preFrobenioid.base.map numerator ≫
                  inv (F.preFrobenioid.base.map denominator))) ≫
              F.preFrobenioid.base.map denominator =
              baseComparison.iso.hom ≫
                ((F.preFrobenioid.base.map numerator ≫
                    inv (F.preFrobenioid.base.map denominator)) ≫
                  F.preFrobenioid.base.map denominator) :=
            Category.assoc _ _ _
          _ = baseComparison.iso.hom ≫
                (F.preFrobenioid.base.map numerator ≫
                  (inv (F.preFrobenioid.base.map denominator) ≫
                    F.preFrobenioid.base.map denominator)) :=
            congrArg (fun arrow ↦ baseComparison.iso.hom ≫ arrow)
              (Category.assoc _ _ _)
          _ = baseComparison.iso.hom ≫
                F.preFrobenioid.base.map numerator := by
            rw [IsIso.inv_hom_id, Category.comp_id] }
  let refinementExistence :=
    (numeratorPullback lifted.source).2 comparisonTarget
  let refinement := Classical.choose refinementExistence
  have refinementComparison := Classical.choose_spec refinementExistence
  have refinementCommutes :
      refinement ≫ numerator = lifted.hom ≫ denominator := by
    have equation := congrArg
      (fun value ↦ value.toCodomain) refinementComparison
    exact equation
  have refinementBase :
      F.preFrobenioid.base.map refinement = baseComparison.iso.hom := by
    have equation := congrArg
      (fun value ↦ value.toBaseDomain) refinementComparison
    exact equation
  have numeratorProperties :=
    F.axioms.pullback_linear_lbInvertible numerator numeratorPullback
  have liftedProperties :=
    F.axioms.pullback_linear_lbInvertible lifted.hom liftedPullback
  have refinementLinear : F.preFrobenioid.IsLinear refinement := by
    have degreeEquation := congrArg F.preFrobenioid.frobeniusDegree
      refinementCommutes
    rw [F.preFrobenioid.frobeniusDegree_comp,
      F.preFrobenioid.frobeniusDegree_comp,
      numeratorProperties.1, liftedProperties.1,
      denominatorProperty.1.1] at degreeEquation
    simpa using degreeEquation
  have refinementBaseIso : F.preFrobenioid.IsBaseIso refinement := by
    change IsIso (F.preFrobenioid.base.map refinement)
    rw [refinementBase]
    infer_instance
  have compositeCoAngular :
      F.preFrobenioid.IsCoAngular (refinement ≫ numerator) := by
    rw [refinementCommutes]
    exact F.axioms.coAngular_comp lifted.hom denominator
      liftedProperties.2.1 denominatorProperty.2
  exact
    { source := lifted.source
      refinement := refinement
      refinement_property :=
        ⟨⟨refinementLinear, refinementBaseIso⟩,
          isCoAngular_left_of_comp_linear F refinement numerator
            refinementBaseIso numeratorProperties.1 compositeCoAngular⟩
      across := lifted.hom
      commutes := refinementCommutes }

/-- Proposition 1.11(vii) for an arbitrary pre-step numerator, obtained by
the co-angular-then-isometric factorization of Definition 1.3(v)(c) and
pasting the two primitive squares. -/
def rightOreSquare_preStep
    {A B C : F.carrier} (denominator : A ⟶ B) (numerator : C ⟶ B)
    (denominatorProperty : denominators F denominator)
    (numeratorPreStep : F.preFrobenioid.IsPreStep numerator) :
    RightOreSquare F denominator numerator := by
  let factorizationExistence :=
    F.axioms.preStep_coAngularThenIsometric numerator numeratorPreStep
  let factorization := Classical.choice factorizationExistence
  have firstCoAngular :
      F.preFrobenioid.IsCoAngular factorization.first := by
    exact factorization.first_kind
  have secondIsometric :
      F.preFrobenioid.IsIsometric factorization.second := by
    exact factorization.second_kind
  let outer := rightOreSquare_isometricPreStep F denominator
    factorization.second denominatorProperty factorization.second_preStep
      secondIsometric
  let inner := rightOreSquare_coAngularPreStep F outer.refinement
    factorization.first outer.refinement_property
      ⟨factorization.first_preStep, firstCoAngular⟩
  let pasted := RightOreSquare.paste F denominator
    factorization.first factorization.second outer inner
  exact
    { source := pasted.source
      refinement := pasted.refinement
      refinement_property := pasted.refinement_property
      across := pasted.across
      commutes := by
        calc
          pasted.refinement ≫ numerator =
              pasted.refinement ≫
                (factorization.first ≫ factorization.second) :=
            congrArg (fun arrow ↦ pasted.refinement ≫ arrow)
              factorization.composite.symm
          _ = pasted.across ≫ denominator := pasted.commutes }

/-- Proposition 1.11(vii) for a morphism of Frobenius type.  The denominator
is first refined to the incoming divisor `d • Z`.  A co-angular pre-step over
the numerator domain represents the pullback of `Z`; after a Definition
1.3(iv) factorization, its post-Frobenius pre-step has incoming divisor
`d • Z` and is therefore uniquely isomorphic to the refined denominator. -/
def rightOreSquare_frobenius
    {A B C : F.carrier} (denominator : A ⟶ B) (numerator : C ⟶ B)
    (denominatorProperty : denominators F denominator)
    (numeratorFrobenius : F.preFrobenioid.IsOfFrobeniusType numerator) :
    RightOreSquare F denominator numerator := by
  let denominatorDivisorExistence :=
    F.axioms.incomingDivisor denominator denominatorProperty.1
      denominatorProperty.2
  let denominatorDivisor := Classical.choose denominatorDivisorExistence
  have denominatorDivisorEquation :=
    (Classical.choose_spec denominatorDivisorExistence).1
  let denominatorIncoming :
      F.preFrobenioid.IncomingCoAngularPreStep B denominatorDivisor :=
    { source := A
      hom := denominator
      preStep := denominatorProperty.1
      coAngular := denominatorProperty.2
      pulledBack_divisor_eq := denominatorDivisorEquation }
  let degree := (F.preFrobenioid.frobeniusDegree numerator).1
  let scaledDivisor := degree • denominatorDivisor
  let scaledIncoming :=
    F.axioms.incomingDivisorRepresentative B scaledDivisor
  have denominatorLeScaled : denominatorDivisor ≤ scaledDivisor := by
    refine ⟨(degree - 1) • denominatorDivisor, ?_⟩
    change degree • denominatorDivisor =
      denominatorDivisor + (degree - 1) • denominatorDivisor
    have positive := (F.preFrobenioid.frobeniusDegree numerator).2
    have degreeEquation : degree - 1 + 1 = degree := by
      exact Nat.succ_pred_eq_of_pos positive
    calc
      degree • denominatorDivisor =
          (degree - 1 + 1) • denominatorDivisor :=
        congrArg (fun value ↦ value • denominatorDivisor)
          degreeEquation.symm
      _ = denominatorDivisor + (degree - 1) • denominatorDivisor :=
        succ_nsmul' _ _
  let toDenominatorExistence :=
    (F.axioms.incomingDivisorOrderFullyFaithful scaledIncoming
      denominatorIncoming).1 denominatorLeScaled
  let toDenominator := Classical.choose toDenominatorExistence
  have toDenominatorCommutes :=
    (Classical.choose_spec toDenominatorExistence).1
  let pulledDivisor := F.preFrobenioid.divisorMonoid.pullback
    (F.preFrobenioid.base.map numerator) denominatorDivisor
  let refinementRepresentative :=
    F.axioms.incomingDivisorRepresentative C pulledDivisor
  have compositeCoAngular :
      F.preFrobenioid.IsCoAngular
        (refinementRepresentative.hom ≫ numerator) :=
    F.axioms.coAngular_comp refinementRepresentative.hom numerator
      refinementRepresentative.coAngular numeratorFrobenius.1.1
  have compositeIncomingEquation :
      F.preFrobenioid.divisorMonoid.pullback
          (F.preFrobenioid.base.map
            (refinementRepresentative.hom ≫ numerator))
          scaledDivisor =
        F.preFrobenioid.divisor
          (refinementRepresentative.hom ≫ numerator) := by
    rw [F.preFrobenioid.base.map_comp,
      F.preFrobenioid.divisorMonoid.pullback_comp,
      F.preFrobenioid.divisor_comp,
      numeratorFrobenius.1.2]
    change
      F.preFrobenioid.divisorMonoid.pullback
          (F.preFrobenioid.base.map refinementRepresentative.hom)
          (F.preFrobenioid.divisorMonoid.pullback
            (F.preFrobenioid.base.map numerator) scaledDivisor) =
        F.preFrobenioid.divisorMonoid.pullback
            (F.preFrobenioid.base.map refinementRepresentative.hom) 0 +
          (F.preFrobenioid.frobeniusDegree numerator).1 •
            F.preFrobenioid.divisor refinementRepresentative.hom
    dsimp only [scaledDivisor, degree]
    rw [map_nsmul, map_nsmul]
    change
      (F.preFrobenioid.frobeniusDegree numerator).1 •
          F.preFrobenioid.divisorMonoid.pullback
            (F.preFrobenioid.base.map refinementRepresentative.hom)
            pulledDivisor =
        F.preFrobenioid.divisorMonoid.pullback
            (F.preFrobenioid.base.map refinementRepresentative.hom) 0 +
          (F.preFrobenioid.frobeniusDegree numerator).1 •
            F.preFrobenioid.divisor refinementRepresentative.hom
    rw [refinementRepresentative.pulledBack_divisor_eq,
      map_zero, zero_add]
  let factorizationExistence :=
    F.axioms.factorization (refinementRepresentative.hom ≫ numerator)
  let factorization := Classical.choice factorizationExistence
  have compositeBaseIso : F.preFrobenioid.IsBaseIso
      (refinementRepresentative.hom ≫ numerator) := by
    change IsIso
      (F.preFrobenioid.base.map
        (refinementRepresentative.hom ≫ numerator))
    rw [F.preFrobenioid.base.map_comp]
    haveI : IsIso
        (F.preFrobenioid.base.map refinementRepresentative.hom) :=
      refinementRepresentative.preStep.2
    haveI : IsIso (F.preFrobenioid.base.map numerator) :=
      numeratorFrobenius.2
    infer_instance
  have pullbackBaseIso :
      F.preFrobenioid.IsBaseIso factorization.pullback := by
    change IsIso (F.preFrobenioid.base.map factorization.pullback)
    haveI : IsIso
        (F.preFrobenioid.base.map factorization.frobenius) :=
      factorization.frobenius_type.2
    haveI : IsIso
        (F.preFrobenioid.base.map factorization.preStep) :=
      factorization.preStep_type.2
    haveI : IsIso
        (F.preFrobenioid.base.map
          (refinementRepresentative.hom ≫ numerator)) :=
      compositeBaseIso
    have totalArrowEquation :
        (factorization.frobenius ≫ factorization.preStep) ≫
            factorization.pullback =
          refinementRepresentative.hom ≫ numerator := by
      rw [Category.assoc]
      exact factorization.composite
    haveI : IsIso
        (F.preFrobenioid.base.map
          ((factorization.frobenius ≫ factorization.preStep) ≫
            factorization.pullback)) := by
      rw [congrArg F.preFrobenioid.base.map totalArrowEquation]
      infer_instance
    haveI : IsIso
        (F.preFrobenioid.base.map
          (factorization.frobenius ≫ factorization.preStep)) := by
      rw [F.preFrobenioid.base.map_comp]
      infer_instance
    exact IsIso.of_isIso_fac_left
      (f := F.preFrobenioid.base.map
        (factorization.frobenius ≫ factorization.preStep))
      (g := F.preFrobenioid.base.map factorization.pullback)
      (h := F.preFrobenioid.base.map
        ((factorization.frobenius ≫ factorization.preStep) ≫
          factorization.pullback))
      (F.preFrobenioid.base.map_comp
        (factorization.frobenius ≫ factorization.preStep)
        factorization.pullback).symm
  have pullbackIso := isIso_of_pullback_baseIso F factorization.pullback
    factorization.pullback_type pullbackBaseIso
  letI : IsIso factorization.pullback := pullbackIso
  have pullbackProperty : denominators F factorization.pullback :=
    ⟨isPreStep_of_isIso F factorization.pullback,
      isCoAngular_of_isIso F factorization.pullback⟩
  have factorizationPreStepCoAngular :
      F.preFrobenioid.IsCoAngular factorization.preStep := by
    intro U V gamma beta alpha equality alphaLinear betaPreStep
      betaIsometric baseAlternative
    exact factorization_preStep_coAngular F factorization compositeCoAngular
      pullbackIso gamma beta alpha equality alphaLinear betaPreStep
        betaIsometric baseAlternative
  let postStep := factorization.preStep ≫ factorization.pullback
  have postStepProperty : denominators F postStep :=
    denominators_comp F factorization.preStep factorization.pullback
      ⟨factorization.preStep_type, factorizationPreStepCoAngular⟩
      pullbackProperty
  have factorizationComposite :
      factorization.frobenius ≫ postStep =
        refinementRepresentative.hom ≫ numerator := by
    dsimp [postStep]
    simpa only [Category.assoc] using factorization.composite
  have factorizationIncomingEquation :
      F.preFrobenioid.divisorMonoid.pullback
          (F.preFrobenioid.base.map
            (factorization.frobenius ≫ postStep)) scaledDivisor =
        F.preFrobenioid.divisor
          (factorization.frobenius ≫ postStep) := by
    rw [factorizationComposite]
    exact compositeIncomingEquation
  have postStepIncomingEquation :
      F.preFrobenioid.divisorMonoid.pullback
          (F.preFrobenioid.base.map postStep) scaledDivisor =
        F.preFrobenioid.divisor postStep := by
    apply F.preFrobenioid.divisorMonoid.characteristicallyInjective
      (F.preFrobenioid.base.map factorization.frobenius)
    have equation := factorizationIncomingEquation
    rw [F.preFrobenioid.base.map_comp,
      F.preFrobenioid.divisorMonoid.pullback_comp,
      F.preFrobenioid.divisor_comp,
      postStepProperty.1.1, factorization.frobenius_type.1.2] at equation
    simpa using equation
  let postStepIncoming :
      F.preFrobenioid.IncomingCoAngularPreStep B scaledDivisor :=
    { source := factorization.frobeniusCodomain
      hom := postStep
      preStep := postStepProperty.1
      coAngular := postStepProperty.2
      pulledBack_divisor_eq := postStepIncomingEquation }
  let postStepComparisonExistence :=
    F.axioms.incomingDivisorRepresentative_unique
      postStepIncoming scaledIncoming
  let postStepComparison := Classical.choose postStepComparisonExistence
  have postStepComparisonCommutes :=
    (Classical.choose_spec postStepComparisonExistence).1
  exact
    { source := refinementRepresentative.source
      refinement := refinementRepresentative.hom
      refinement_property :=
        ⟨refinementRepresentative.preStep,
          refinementRepresentative.coAngular⟩
      across := factorization.frobenius ≫
        postStepComparison.hom ≫ toDenominator
      commutes := by
        calc
          refinementRepresentative.hom ≫ numerator =
              factorization.frobenius ≫ postStep :=
            factorizationComposite.symm
          _ = factorization.frobenius ≫
              (postStepComparison.hom ≫ scaledIncoming.hom) :=
            congrArg (fun arrow ↦ factorization.frobenius ≫ arrow)
              postStepComparisonCommutes.symm
          _ = factorization.frobenius ≫
              (postStepComparison.hom ≫
                (toDenominator ≫ denominator)) :=
            congrArg
              (fun arrow ↦ factorization.frobenius ≫
                (postStepComparison.hom ≫ arrow))
              toDenominatorCommutes.symm
          _ = (factorization.frobenius ≫
                postStepComparison.hom ≫ toDenominator) ≫ denominator := by
            simp only [Category.assoc] }

/-- The complete Proposition 1.11(vii) square, obtained by applying the
Definition 1.3(iv) Frobenius/pre-step/pull-back factorization to the numerator
and pasting the three source-derived squares. -/
def rightOreSquare
    {A B C : F.carrier} (denominator : A ⟶ B) (numerator : C ⟶ B)
    (denominatorProperty : denominators F denominator) :
    RightOreSquare F denominator numerator := by
  let factorizationExistence := F.axioms.factorization numerator
  let factorization := Classical.choice factorizationExistence
  let pullbackSquare := rightOreSquare_pullback F denominator
    factorization.pullback denominatorProperty factorization.pullback_type
  let preStepSquare := rightOreSquare_preStep F pullbackSquare.refinement
    factorization.preStep pullbackSquare.refinement_property
      factorization.preStep_type
  let tailSquare := RightOreSquare.paste F denominator
    factorization.preStep factorization.pullback pullbackSquare preStepSquare
  let frobeniusSquare := rightOreSquare_frobenius F tailSquare.refinement
    factorization.frobenius tailSquare.refinement_property
      factorization.frobenius_type
  let completeSquare := RightOreSquare.paste F denominator
    factorization.frobenius
      (factorization.preStep ≫ factorization.pullback)
      tailSquare frobeniusSquare
  exact
    { source := completeSquare.source
      refinement := completeSquare.refinement
      refinement_property := completeSquare.refinement_property
      across := completeSquare.across
      commutes := by
        calc
          completeSquare.refinement ≫ numerator =
              completeSquare.refinement ≫
                (factorization.frobenius ≫
                  factorization.preStep ≫ factorization.pullback) :=
            congrArg (fun arrow ↦ completeSquare.refinement ≫ arrow)
              factorization.composite.symm
          _ = completeSquare.across ≫ denominator :=
            completeSquare.commutes }

/-- Frobenioids I, Proposition 1.11(vii), derived from the arbitrary
`FrobenioidPresentation` axioms. -/
theorem hasCoAngularPreStepSquares : HasCoAngularPreStepSquares F := by
  intro A B C denominator denominatorProperty numerator
  let square := rightOreSquare F denominator numerator denominatorProperty
  exact ⟨square.source, square.refinement, square.refinement_property,
    square.across, square.commutes⟩

/-- Proposition 1.11(vii) supplies the right calculus of fractions used in
Proposition 4.4(i). -/
@[reducible] def hasRightCalculusOfFractions
    : (denominators F).HasRightCalculusOfFractions where
  id_mem := denominators_id F
  comp_mem := denominators_comp F
  exists_rightFraction X Y fraction := by
    obtain ⟨D, refinement, hrefinement, across, square⟩ :=
      hasCoAngularPreStepSquares F fraction.s fraction.hs fraction.f
    exact ⟨⟨refinement, hrefinement, across⟩, square⟩
  ext X Y Y' first second denominator hdenominator equality := by
    haveI : Mono denominator :=
      F.axioms.preStep_mono denominator hdenominator.1
    have arrowsEqual : first = second := (cancel_mono denominator).1 equality
    exact ⟨_, 𝟙 _, denominators_id F _, by simp [arrowsEqual]⟩

/-- The arbitrary Frobenioid's birational category, before choosing roof
coordinates. -/
abbrev BirationalCategory := (denominators F).Localization

/-- The canonical localization `C → C^birat`. -/
abbrev localizationFunctor :
    (F.carrier : Type u) ⥤ BirationalCategory F :=
  (denominators F).Q

/-- The birational localization is connected because it has the same objects
as the source up to the canonical localization object equivalence, and every
source zigzag remains a zigzag after localization. -/
theorem birationalCategory_isConnected :
    IsConnected (BirationalCategory F) := by
  letI : IsConnected F.carrier := F.carrierConnected
  let objectEquiv := Localization.Construction.objEquiv (denominators F)
  letI : Nonempty (BirationalCategory F) :=
    ⟨objectEquiv (Classical.choice (inferInstance : Nonempty F.carrier))⟩
  apply IsConnected.of_any_functor_const_on_obj
  intro alpha functor first second
  have sourceEquality := any_functor_const_on_obj
    (localizationFunctor F ⋙ functor)
    (objectEquiv.symm first) (objectEquiv.symm second)
  simpa [objectEquiv] using sourceEquality

/-- A co-angular pre-step with fixed codomain, i.e. an object of the
indexing category `C_A^{coa-pre}` in Proposition 4.4. -/
structure CoAngularPreStepOver (target : F.carrier) where
  source : F.carrier
  hom : source ⟶ target
  property : denominators F hom

namespace CoAngularPreStepOver

/-- Morphisms are the morphisms of the ambient slice category.  No extra
condition is added: both composites are already co-angular pre-steps. -/
@[ext]
structure Transition {target : F.carrier}
    (first second : CoAngularPreStepOver F target) where
  hom : first.source ⟶ second.source
  commutes : hom ≫ second.hom = first.hom

instance category (target : F.carrier) :
    Category.{u} (CoAngularPreStepOver F target) where
  Hom := Transition F
  id object := ⟨𝟙 object.source, Category.id_comp object.hom⟩
  comp first second :=
    ⟨first.hom ≫ second.hom, by
      rw [Category.assoc, second.commutes, first.commutes]⟩
  id_comp arrow := by ext; exact Category.id_comp arrow.hom
  comp_id arrow := by ext; exact Category.comp_id arrow.hom
  assoc first second third := by ext; exact Category.assoc _ _ _

/-- The identity denominator. -/
def identity (target : F.carrier) : CoAngularPreStepOver F target where
  source := target
  hom := 𝟙 target
  property := denominators_id F target

/-- The Hom-set diagram whose transition maps precompose numerators. -/
def homDiagram (source target : F.carrier) :
    (CoAngularPreStepOver F source)ᵒᵖ ⥤ Type u where
  obj index := index.unop.source ⟶ target
  map transition := ↾(fun numerator ↦ transition.unop.hom ≫ numerator)
  map_id _ := by
    ext numerator
    exact Category.id_comp numerator
  map_comp first second := by
    ext numerator
    exact Category.assoc _ _ _

/-- Proposition 1.11(vii) makes the direct-limit index filtered. -/
@[reducible] def indexIsFiltered (source : F.carrier)
    : IsFiltered (CoAngularPreStepOver F source)ᵒᵖ where
  cocone_objs first second := by
    obtain ⟨D, refinement, hrefinement, across, square⟩ :=
      hasCoAngularPreStepSquares F second.unop.hom
        second.unop.property first.unop.hom
    let common : CoAngularPreStepOver F source :=
      { source := D
        hom := refinement ≫ first.unop.hom
        property := denominators_comp F refinement first.unop.hom
          hrefinement first.unop.property }
    let toFirst : common ⟶ first.unop :=
      { hom := refinement
        commutes := rfl }
    let toSecond : common ⟶ second.unop :=
      { hom := across
        commutes := by simpa [common] using square.symm }
    exact ⟨Opposite.op common, toFirst.op, toSecond.op, trivial⟩
  cocone_maps {first second} left right := by
    haveI : Mono first.unop.hom :=
      F.axioms.preStep_mono first.unop.hom first.unop.property.1
    have unopEquality : left.unop = right.unop := by
      apply Transition.ext (F := F)
      apply (cancel_mono first.unop.hom).1
      rw [left.unop.commutes, right.unop.commutes]
    have equality : left = right := Quiver.Hom.unop_inj unopEquality
    subst right
    exact ⟨second, 𝟙 second, rfl⟩
  nonempty := ⟨Opposite.op (identity F source)⟩

/-- Evaluation of a roof as `Q(denominator)^{-1} ∘ Q(numerator)`. -/
def roofValue
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    (localizationFunctor F).obj source ⟶
      (localizationFunctor F).obj target :=
  (MorphismProperty.RightFraction.mk denominator.hom
      denominator.property numerator).map
    (localizationFunctor F) (MorphismProperty.Q_inverts (denominators F))

/-- Roof evaluation respects a refinement in the indexing category. -/
theorem roofValue_transition
    {source target : F.carrier}
    {first second : CoAngularPreStepOver F source}
    (transition : first ⟶ second)
    (numerator : second.source ⟶ target) :
    roofValue F first (transition.hom ≫ numerator) =
      roofValue F second numerator := by
  letI := hasRightCalculusOfFractions F
  unfold roofValue
  apply (MorphismProperty.RightFraction.map_eq_iff
    (L := localizationFunctor F) (W := denominators F) _ _).2
  exact ⟨first.source, 𝟙 first.source, transition.hom,
    by simpa using transition.commutes.symm,
    by simp, by simpa using first.property⟩

/-- Roof evaluation is a cocone over the Hom-set diagram. -/
def homCocone (source target : F.carrier) :
    Limits.Cocone (homDiagram F source target) where
  pt := ((localizationFunctor F).obj source ⟶
    (localizationFunctor F).obj target)
  ι :=
    { app index := ↾(fun numerator ↦ roofValue F index.unop numerator)
      naturality := by
        intro first second transition
        ext numerator
        exact roofValue_transition F transition.unop numerator }

/-- Proposition 4.4's literal filtered Hom colimit. -/
abbrev BirationalHomColimit (source target : F.carrier) :=
  Limits.colimit (homDiagram F source target)

/-- Comparison from the paper's direct limit to the categorical
localization. -/
def colimitComparison (source target : F.carrier) :
    BirationalHomColimit F source target →
      ((localizationFunctor F).obj source ⟶
        (localizationFunctor F).obj target) :=
  fun value ↦ Limits.colimit.desc (homDiagram F source target)
    (homCocone F source target) value

@[simp]
theorem colimitComparison_ι
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    colimitComparison F source target
        (Limits.colimit.ι (homDiagram F source target)
          (Opposite.op denominator) numerator) =
      roofValue F denominator numerator := by
  exact ConcreteCategory.congr_hom
    (Limits.colimit.ι_desc (homCocone F source target)
      (Opposite.op denominator)) numerator

/-- Every localized arrow has a roof representative, hence comes from the
source Hom colimit. -/
theorem colimitComparison_surjective
    (source target : F.carrier) :
    Function.Surjective (colimitComparison F source target) := by
  letI := hasRightCalculusOfFractions F
  intro arrow
  obtain ⟨fraction, represents⟩ :=
    Localization.exists_rightFraction
      (L := localizationFunctor F) (W := denominators F) arrow
  let denominator : CoAngularPreStepOver F source :=
    { source := fraction.X'
      hom := fraction.s
      property := fraction.hs }
  refine ⟨Limits.colimit.ι (homDiagram F source target)
    (Opposite.op denominator) fraction.f, ?_⟩
  rw [colimitComparison_ι]
  exact represents.symm

/-- Equality of localized roofs is exactly equality after a common
refinement, so the Hom-colimit comparison is injective. -/
theorem colimitComparison_injective
    (source target : F.carrier) :
    Function.Injective (colimitComparison F source target) := by
  letI := hasRightCalculusOfFractions F
  letI := indexIsFiltered F source
  intro left right equality
  rcases Limits.Types.jointly_surjective' left with
    ⟨firstIndex, firstNumerator, firstRepresents⟩
  rcases Limits.Types.jointly_surjective' right with
    ⟨secondIndex, secondNumerator, secondRepresents⟩
  rw [← firstRepresents, ← secondRepresents] at equality ⊢
  rw [colimitComparison_ι, colimitComparison_ι] at equality
  unfold roofValue at equality
  have fractionRelation :=
    (MorphismProperty.RightFraction.map_eq_iff
      (L := localizationFunctor F) (W := denominators F) _ _).1 equality
  rcases fractionRelation with
    ⟨commonSource, toFirst, toSecond, denominatorEquality,
      numeratorEquality, commonProperty⟩
  let common : CoAngularPreStepOver F source :=
    { source := commonSource
      hom := toFirst ≫ firstIndex.unop.hom
      property := commonProperty }
  let firstTransition : common ⟶ firstIndex.unop :=
    { hom := toFirst
      commutes := rfl }
  let secondTransition : common ⟶ secondIndex.unop :=
    { hom := toSecond
      commutes := by
        simpa [common] using denominatorEquality.symm }
  apply Limits.Types.colimit_sound'
    (f := firstTransition.op) (f' := secondTransition.op)
  exact numeratorEquality

/-- The direct-limit Hom set of Proposition 4.4 is canonically the Hom set
of the arbitrary categorical localization. -/
def colimitComparisonEquiv
    (source target : F.carrier) :
    BirationalHomColimit F source target ≃
      ((localizationFunctor F).obj source ⟶
        (localizationFunctor F).obj target) :=
  Equiv.ofBijective (colimitComparison F source target)
    ⟨colimitComparison_injective F source target,
      colimitComparison_surjective F source target⟩

@[simp]
theorem colimitComparisonEquiv_ι
    {source target : F.carrier}
    (denominator : CoAngularPreStepOver F source)
    (numerator : denominator.source ⟶ target) :
    colimitComparisonEquiv F source target
        (Limits.colimit.ι (homDiagram F source target)
          (Opposite.op denominator) numerator) =
      roofValue F denominator numerator :=
  colimitComparison_ι F denominator numerator

end CoAngularPreStepOver

/-- Forget the effective divisor while retaining the base arrow and
Frobenius degree.  This is the upper horizontal arrow
`F_Φ → F_{Φᵍᵖ} → F_{0_D}` after composition with the source
structure functor. -/
def forgetDivisorFunctor :
    (F.carrier : Type u) ⥤
      ElementaryFrobenioid F.baseCategory F.isFSM
        (zeroDivisorialMonoidOn F.baseCategory F.isFSM) where
  obj object := F.preFrobenioid.base.obj object
  map arrow :=
    { base := F.preFrobenioid.base.map arrow
      divisor := default
      frobeniusDegree := F.preFrobenioid.frobeniusDegree arrow }
  map_id object := by
    apply ElementaryFrobenioidHom.ext
    · exact F.preFrobenioid.base.map_id object
    · exact Subsingleton.elim _ _
    · exact F.preFrobenioid.frobeniusDegree_id object
  map_comp first second := by
    apply ElementaryFrobenioidHom.ext
    · exact F.preFrobenioid.base.map_comp first second
    · exact Subsingleton.elim _ _
    · exact F.preFrobenioid.frobeniusDegree_comp first second

/-- The upper route `C → F_(Phi^gp)` in Proposition 4.4(i), obtained by
groupifying the source divisor coordinate. -/
def groupifiedStructureFunctor :
    (F.carrier : Type u) ⥤
      GroupifiedElementaryFrobenioid F.preFrobenioid.divisorMonoid where
  obj object := ⟨F.preFrobenioid.base.obj object⟩
  map arrow :=
    { base := F.preFrobenioid.base.map arrow
      divisor := Algebra.GrothendieckAddGroup.of
        (F.preFrobenioid.divisor arrow)
      frobeniusDegree := F.preFrobenioid.frobeniusDegree arrow }
  map_id object := by
    apply GroupifiedElementaryHom.ext
    · exact F.preFrobenioid.base.map_id object
    · rw [F.preFrobenioid.divisor_id]
      exact map_zero _
    · exact F.preFrobenioid.frobeniusDegree_id object
  map_comp first second := by
    apply GroupifiedElementaryHom.ext
    · exact F.preFrobenioid.base.map_comp first second
    · change Algebra.GrothendieckAddGroup.of
          (F.preFrobenioid.divisor (first ≫ second)) =
        F.preFrobenioid.divisorMonoid.gpPullback
            (F.preFrobenioid.base.map first)
            (Algebra.GrothendieckAddGroup.of
              (F.preFrobenioid.divisor second)) +
          (F.preFrobenioid.frobeniusDegree second).1 •
            Algebra.GrothendieckAddGroup.of
              (F.preFrobenioid.divisor first)
      rw [F.preFrobenioid.divisor_comp,
        map_add, map_nsmul,
        F.preFrobenioid.divisorMonoid.gpPullback_of]
    · exact F.preFrobenioid.frobeniusDegree_comp first second

/-- In a groupified elementary category, a degree-one arrow over a base
isomorphism is invertible; its inverse carries the expected negative pulled
back divisor. -/
def groupifiedArrowIso
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (baseIso : F.preFrobenioid.IsBaseIso arrow) :
    (groupifiedStructureFunctor F).obj X ≅
      (groupifiedStructureFunctor F).obj Y := by
  change IsIso (F.preFrobenioid.base.map arrow) at baseIso
  let baseInverse := Classical.choose baseIso.out
  have homInv := (Classical.choose_spec baseIso.out).1
  have invHom := (Classical.choose_spec baseIso.out).2
  let hom := (groupifiedStructureFunctor F).map arrow
  let divisor := Algebra.GrothendieckAddGroup.of
    (F.preFrobenioid.divisor arrow)
  let inverse : (groupifiedStructureFunctor F).obj Y ⟶
      (groupifiedStructureFunctor F).obj X :=
    { base := baseInverse
      divisor := -F.preFrobenioid.divisorMonoid.gpPullback
        baseInverse divisor
      frobeniusDegree := 1 }
  refine
    { hom := hom
      inv := inverse
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply GroupifiedElementaryHom.ext
    · dsimp [hom, inverse, groupifiedStructureFunctor]
      exact homInv
    · change (GroupifiedElementaryHom.comp
          F.preFrobenioid.divisorMonoid hom inverse).divisor = 0
      dsimp [GroupifiedElementaryHom.comp, hom, inverse,
        groupifiedStructureFunctor]
      rw [show (1 : ℕ+).1 = 1 by rfl, one_nsmul]
      change F.preFrobenioid.divisorMonoid.gpPullback
            (F.preFrobenioid.base.map arrow)
            (-F.preFrobenioid.divisorMonoid.gpPullback
              baseInverse divisor) +
          divisor = 0
      rw [map_neg]
      change -((F.preFrobenioid.divisorMonoid.gpPullback
            (F.preFrobenioid.base.map arrow)).comp
          (F.preFrobenioid.divisorMonoid.gpPullback
            baseInverse)) divisor + divisor = 0
      rw [← F.preFrobenioid.divisorMonoid.gpPullback_comp,
        homInv,
        F.preFrobenioid.divisorMonoid.gpPullback_id]
      simp
    · dsimp [hom, inverse, groupifiedStructureFunctor]
      change F.preFrobenioid.frobeniusDegree arrow * 1 = 1
      rw [linear]
      rfl
  · apply GroupifiedElementaryHom.ext
    · dsimp [hom, inverse, groupifiedStructureFunctor]
      exact invHom
    · change (GroupifiedElementaryHom.comp
          F.preFrobenioid.divisorMonoid inverse hom).divisor = 0
      dsimp [GroupifiedElementaryHom.comp, hom, inverse,
        groupifiedStructureFunctor]
      change F.preFrobenioid.divisorMonoid.gpPullback
            baseInverse divisor +
          (F.preFrobenioid.frobeniusDegree arrow).1 •
            (-F.preFrobenioid.divisorMonoid.gpPullback
              baseInverse divisor) = 0
      rw [linear]
      rw [show (1 : ℕ+).1 = 1 by rfl, one_nsmul]
      exact add_neg_cancel _
    · dsimp [hom, inverse, groupifiedStructureFunctor]
      change 1 * F.preFrobenioid.frobeniusDegree arrow = 1
      rw [linear]
      rfl

/-- The groupified source structure functor inverts every co-angular
pre-step. -/
theorem groupifiedStructureFunctor_inverts :
    (denominators F).IsInvertedBy (groupifiedStructureFunctor F) := by
  intro X Y arrow denominator
  change IsIso
    (groupifiedArrowIso F arrow denominator.1.1 denominator.1.2).hom
  infer_instance

/-- The lower route `C^birat → F_(Phi^gp)` in Proposition 4.4(i). -/
def groupifiedBirationalFunctor :
    BirationalCategory F ⥤
      GroupifiedElementaryFrobenioid F.preFrobenioid.divisorMonoid :=
  Localization.Construction.lift (groupifiedStructureFunctor F)
    (groupifiedStructureFunctor_inverts F)

/-- The upper-left square through `F_(Phi^gp)` commutes. -/
theorem groupifiedBirationalFunctor_fac :
    localizationFunctor F ⋙ groupifiedBirationalFunctor F =
      groupifiedStructureFunctor F :=
  Localization.Construction.fac _ _

/-- The groupified divisor of a localized source arrow is its source divisor
in the objectwise Grothendieck group. -/
theorem groupifiedBirationalFunctor_map_localizationFunctor_divisor
    {X Y : F.carrier} (arrow : X ⟶ Y) :
    ((groupifiedBirationalFunctor F).map
      ((localizationFunctor F).map arrow)).divisor =
        Algebra.GrothendieckAddGroup.of
          (F.preFrobenioid.divisor arrow) := by
  simp only [groupifiedBirationalFunctor, localizationFunctor,
    groupifiedStructureFunctor, Localization.Construction.lift]
  dsimp [MorphismProperty.Q, CategoryTheory.Quotient.lift,
    Quot.liftOn, Quotient.functor]
  rw [CategoryTheory.composePath_toPath]

/-- The groupified target functor retains the base arrow of a localized
source arrow. -/
theorem groupifiedBirationalFunctor_map_localizationFunctor_base
    {X Y : F.carrier} (arrow : X ⟶ Y) :
    ((groupifiedBirationalFunctor F).map
      ((localizationFunctor F).map arrow)).base =
        F.preFrobenioid.base.map arrow := by
  simp only [groupifiedBirationalFunctor, localizationFunctor,
    groupifiedStructureFunctor, Localization.Construction.lift]
  dsimp [MorphismProperty.Q, CategoryTheory.Quotient.lift,
    Quot.liftOn, Quotient.functor]
  rw [CategoryTheory.composePath_toPath]

/-- The groupified target functor retains the Frobenius degree of a localized
source arrow. -/
theorem groupifiedBirationalFunctor_map_localizationFunctor_frobeniusDegree
    {X Y : F.carrier} (arrow : X ⟶ Y) :
    ((groupifiedBirationalFunctor F).map
      ((localizationFunctor F).map arrow)).frobeniusDegree =
        F.preFrobenioid.frobeniusDegree arrow := by
  simp only [groupifiedBirationalFunctor, localizationFunctor,
    groupifiedStructureFunctor, Localization.Construction.lift]
  dsimp [MorphismProperty.Q, CategoryTheory.Quotient.lift,
    Quot.liftOn, Quotient.functor]
  rw [CategoryTheory.composePath_toPath]

/-- The canonical functor `F_(Phi^gp) → F_(0_D)` in Proposition 4.4(i). -/
def groupifiedToZeroFunctor :
    GroupifiedElementaryFrobenioid F.preFrobenioid.divisorMonoid ⥤
      ElementaryFrobenioid F.baseCategory F.isFSM
        (zeroDivisorialMonoidOn F.baseCategory F.isFSM) where
  obj object := object.base
  map arrow :=
    { base := arrow.base
      divisor := default
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Groupifying and then forgetting the divisor is the direct upper route. -/
theorem groupifiedToZeroFunctor_fac :
    groupifiedStructureFunctor F ⋙ groupifiedToZeroFunctor F =
      forgetDivisorFunctor F := rfl

/-- A zero-divisor elementary arrow of degree one over a base isomorphism is
an isomorphism. -/
def zeroArrowIso
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (baseIso : F.preFrobenioid.IsBaseIso arrow) :
    (forgetDivisorFunctor F).obj X ≅ (forgetDivisorFunctor F).obj Y := by
  change IsIso (F.preFrobenioid.base.map arrow) at baseIso
  let baseInverse := Classical.choose baseIso.out
  have homInv := (Classical.choose_spec baseIso.out).1
  have invHom := (Classical.choose_spec baseIso.out).2
  let hom := (forgetDivisorFunctor F).map arrow
  let inverse : (forgetDivisorFunctor F).obj Y ⟶
      (forgetDivisorFunctor F).obj X :=
    { base := baseInverse
      divisor := default
      frobeniusDegree := 1 }
  refine
    { hom := hom
      inv := inverse
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply ElementaryFrobenioidHom.ext
    · dsimp [hom, inverse, forgetDivisorFunctor]
      exact homInv
    · exact Subsingleton.elim _ _
    · change F.preFrobenioid.frobeniusDegree arrow * 1 = 1
      rw [linear]
      rfl
  · apply ElementaryFrobenioidHom.ext
    · dsimp [hom, inverse, forgetDivisorFunctor]
      exact invHom
    · exact Subsingleton.elim _ _
    · change 1 * F.preFrobenioid.frobeniusDegree arrow = 1
      rw [linear]
      rfl

/-- The divisor-forgetting functor inverts every co-angular pre-step. -/
theorem forgetDivisorFunctor_inverts :
    (denominators F).IsInvertedBy (forgetDivisorFunctor F) := by
  intro X Y arrow denominator
  change IsIso
    (zeroArrowIso F arrow denominator.1.1 denominator.1.2).hom
  infer_instance

/-- The bottom arrow `C^birat → F_{0_D}` in Proposition 4.4(i). -/
def structureFunctor :
    BirationalCategory F ⥤
      ElementaryFrobenioid F.baseCategory F.isFSM
        (zeroDivisorialMonoidOn F.baseCategory F.isFSM) :=
  Localization.Construction.lift (forgetDivisorFunctor F)
    (forgetDivisorFunctor_inverts F)

/-- Proposition 4.4(i)'s commutative square. -/
theorem structureFunctor_fac :
    localizationFunctor F ⋙ structureFunctor F =
      forgetDivisorFunctor F :=
  Localization.Construction.fac _ _

/-- The lower composite through `F_(Phi^gp)` is exactly the direct lower
functor to `F_(0_D)`, completing Proposition 4.4(i)'s generic diagram. -/
theorem structureFunctor_eq_groupifiedComposite :
    groupifiedBirationalFunctor F ⋙ groupifiedToZeroFunctor F =
      structureFunctor F := by
  apply Localization.Construction.uniq
  rw [← Functor.assoc, groupifiedBirationalFunctor_fac,
    groupifiedToZeroFunctor_fac, structureFunctor_fac]

/-- The induced pre-Frobenioid over the terminal divisorial monoid. -/
def preFrobenioid :
    PreFrobenioid (BirationalCategory F) F.baseCategory F.isFSM where
  divisorMonoid := zeroDivisorialMonoidOn F.baseCategory F.isFSM
  structureFunctor := structureFunctor F

/-- The birational target is group-like because its divisor monoid is
terminal. -/
theorem isGroupLikeType : (preFrobenioid F).IsGroupLikeType := by
  intro object value
  cases value
  rfl

/-- Proposition 4.4(ii): the canonical localization is faithful.  Equality
in a right-fraction localization is witnessed after precomposition by a
denominator, and every source arrow is epic. -/
theorem localizationFunctor_faithful
    : (localizationFunctor F).Faithful := by
  letI := hasRightCalculusOfFractions F
  constructor
  intro X Y first second equality
  obtain ⟨Z, denominator, hdenominator, equalized⟩ :=
    (MorphismProperty.map_eq_iff_precomp
      (L := localizationFunctor F) (W := denominators F)
      first second).1 equality
  haveI : Epi denominator := F.carrierTotallyEpimorphic denominator
  exact (cancel_epi denominator).1 equalized

/-- Every co-angular pre-step is inverted by the canonical localization. -/
theorem localization_map_isIso_of_coAngularPreStep
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (preStep : F.preFrobenioid.IsPreStep arrow)
    (coAngular : F.preFrobenioid.IsCoAngular arrow) :
    IsIso ((localizationFunctor F).map arrow) :=
  MorphismProperty.Q_inverts (denominators F) arrow
    ⟨preStep, coAngular⟩

end

end Iut.FrobenioidBirationalization
