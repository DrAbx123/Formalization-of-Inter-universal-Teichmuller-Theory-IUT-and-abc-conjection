/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidFactorizationUniqueness

/-!
# Pre-step factorizations for the source model Frobenioid

This file implements Frobenioids I, Definition 1.3(v).  A model pre-step is
monic.  Its two ordered isometric/co-angular factorizations are obtained by
viewing the arrow as an outgoing or incoming divisor representative and using
the unique representative isomorphism from Definition 1.3(iii)(d).  Comparison
isomorphisms between arbitrary factorizations are constructed explicitly and
are unique by total epimorphic cancellation.
-/

open CategoryTheory
namespace Iut.SourceModelFrobenioid.Carrier
universe u
noncomputable section
variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- Definition 1.3(v)(a) for model pre-steps. -/
theorem preStep_mono
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) : Mono arrow :=
  mono_of_preStep arrow preStep

/-- The base projection of a model-category isomorphism is an isomorphism. -/
theorem isIso_baseIsIso
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    [IsIso arrow] : IsIso arrow.base := by
  apply IsIso.mk
  refine ⟨(inv arrow).base, ?_, ?_⟩
  · have projected := congrArg Hom.base (IsIso.hom_inv_id arrow)
    change arrow.base ≫ (inv arrow).base = 𝟙 (Object.base source) at projected
    exact projected
  · have projected := congrArg Hom.base (IsIso.inv_hom_id_assoc arrow (𝟙 target))
    change (inv arrow).base ≫ arrow.base ≫ 𝟙 (Object.base target) =
      𝟙 (Object.base target) at projected
    simpa only [Category.comp_id] using projected

/-- A pre-step viewed as its outgoing divisor representative. -/
def preStepOutgoingRepresentative
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    (preFrobenioid Phi data).OutgoingCoAngularPreStep source arrow.divisor where
  target := target
  hom := arrow
  preStep := preStep
  coAngular := isCoAngular Phi data arrow
  divisor_eq := rfl

/-- The comparison from the canonical outgoing representative to a pre-step. -/
def coAngularThenIsometricIso
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    outgoingDivisorTarget source arrow.divisor ≅ target :=
  Classical.choose (outgoingDivisorRepresentative_unique
    (outgoingDivisorRepresentative source arrow.divisor)
    (preStepOutgoingRepresentative arrow preStep))

theorem coAngularThenIsometricIso_comp
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    outgoingDivisorArrow source arrow.divisor ≫
        (coAngularThenIsometricIso arrow preStep).hom = arrow :=
  (Classical.choose_spec (outgoingDivisorRepresentative_unique
    (outgoingDivisorRepresentative source arrow.divisor)
    (preStepOutgoingRepresentative arrow preStep))).1

/-- Definition 1.3(v)(c): co-angular followed by isometric. -/
def preStep_coAngularThenIsometric
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    (preFrobenioid Phi data).PreStepFactorization arrow true := by
  let comparison := coAngularThenIsometricIso arrow preStep
  letI : IsIso comparison.hom := inferInstance
  have comparisonType := isIso_linear_isometric comparison.hom
  refine
    { midpoint := outgoingDivisorTarget source arrow.divisor
      first := outgoingDivisorArrow source arrow.divisor
      second := comparison.hom
      first_preStep := ?_
      second_preStep := ?_
      first_kind := ?_
      second_kind := ?_
      composite := coAngularThenIsometricIso_comp arrow preStep }
  · constructor
    · rfl
    · change IsIso (𝟙 (Object.base source))
      infer_instance
  · exact ⟨comparisonType.1, isIso_baseIsIso comparison.hom⟩
  · exact isCoAngular Phi data (outgoingDivisorArrow source arrow.divisor)
  · exact comparisonType.2

/-- The divisor transported to the target of a pre-step. -/
def transportedPreStepDivisor
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    (Phi.obj (Object.base target)).carrier :=
  letI : IsIso arrow.base := preStep.2
  Phi.pullback (inv arrow.base) arrow.divisor

theorem pullback_transportedPreStepDivisor
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    Phi.pullback arrow.base (transportedPreStepDivisor arrow preStep) =
      arrow.divisor := by
  have baseIsIso := preStep.2
  change IsIso arrow.base at baseIsIso
  letI : IsIso arrow.base := baseIsIso
  unfold transportedPreStepDivisor
  change Phi.pullback arrow.base
    (Phi.pullback (inv arrow.base) arrow.divisor) = arrow.divisor
  rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
    IsIso.hom_inv_id, Phi.pullback_id]
  rfl

/-- A pre-step viewed as its incoming transported-divisor representative. -/
def preStepIncomingRepresentative
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    (preFrobenioid Phi data).IncomingCoAngularPreStep target
      (transportedPreStepDivisor arrow preStep) where
  source := source
  hom := arrow
  preStep := preStep
  coAngular := isCoAngular Phi data arrow
  pulledBack_divisor_eq := pullback_transportedPreStepDivisor arrow preStep

/-- The comparison from a pre-step to the canonical incoming representative. -/
def isometricThenCoAngularIso
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    source ≅ incomingDivisorSource target
      (transportedPreStepDivisor arrow preStep) :=
  Classical.choose (incomingDivisorRepresentative_unique
    (preStepIncomingRepresentative arrow preStep)
    (incomingDivisorRepresentative target
      (transportedPreStepDivisor arrow preStep)))

theorem isometricThenCoAngularIso_comp
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    (isometricThenCoAngularIso arrow preStep).hom ≫
        incomingDivisorArrow target
          (transportedPreStepDivisor arrow preStep) = arrow :=
  (Classical.choose_spec (incomingDivisorRepresentative_unique
    (preStepIncomingRepresentative arrow preStep)
    (incomingDivisorRepresentative target
      (transportedPreStepDivisor arrow preStep)))).1

/-- Definition 1.3(v)(b): isometric followed by co-angular. -/
def preStep_isometricThenCoAngular
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    (preFrobenioid Phi data).PreStepFactorization arrow false := by
  let comparison := isometricThenCoAngularIso arrow preStep
  letI : IsIso comparison.hom := inferInstance
  have comparisonType := isIso_linear_isometric comparison.hom
  refine
    { midpoint := incomingDivisorSource target
        (transportedPreStepDivisor arrow preStep)
      first := comparison.hom
      second := incomingDivisorArrow target
        (transportedPreStepDivisor arrow preStep)
      first_preStep := ?_
      second_preStep := ?_
      first_kind := ?_
      second_kind := ?_
      composite := isometricThenCoAngularIso_comp arrow preStep }
  · exact ⟨comparisonType.1, isIso_baseIsIso comparison.hom⟩
  · constructor
    · rfl
    · change IsIso (𝟙 (Object.base target))
      infer_instance
  · exact comparisonType.2
  · exact isCoAngular Phi data (incomingDivisorArrow target
      (transportedPreStepDivisor arrow preStep))

/-- The source-prescribed comparison of two pre-step factorizations. -/
def preStepFactorizationIso
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    {coAngularFirst : Bool}
    (left right : (preFrobenioid Phi data).PreStepFactorization
      arrow coAngularFirst) :
    (preFrobenioid Phi data).PreStepFactorizationIso left right := by
  cases coAngularFirst with
  | false =>
      have leftIsometric :
          (preFrobenioid Phi data).IsIsometric left.first := by
        simpa using left.first_kind
      have rightIsometric :
          (preFrobenioid Phi data).IsIsometric right.first := by
        simpa using right.first_kind
      letI : IsIso left.first :=
        isIso_of_preStep_isometric Phi data left.first
          left.first_preStep leftIsometric
      letI : IsIso right.first :=
        isIso_of_preStep_isometric Phi data right.first
          right.first_preStep rightIsometric
      let comparison := (asIso left.first).symm ≪≫ asIso right.first
      have firstSquare : left.first ≫ comparison.hom = right.first := by
        dsimp only [comparison]
        rw [Iso.trans_hom, Iso.symm_hom]
        simp
      have rightInvSquare : right.first ≫ comparison.inv = left.first := by
        rw [← firstSquare, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      have secondSquare : comparison.inv ≫ left.second = right.second := by
        apply (cancel_epi right.first).mp
        rw [← Category.assoc, rightInvSquare, left.composite,
          right.composite]
      exact
        { midpointIso := comparison
          first_square := firstSquare
          second_square := secondSquare }
  | true =>
      have leftIsometric :
          (preFrobenioid Phi data).IsIsometric left.second := by
        simpa using left.second_kind
      have rightIsometric :
          (preFrobenioid Phi data).IsIsometric right.second := by
        simpa using right.second_kind
      letI : IsIso left.second :=
        isIso_of_preStep_isometric Phi data left.second
          left.second_preStep leftIsometric
      letI : IsIso right.second :=
        isIso_of_preStep_isometric Phi data right.second
          right.second_preStep rightIsometric
      let comparison := asIso left.second ≪≫ (asIso right.second).symm
      have secondSquare : comparison.inv ≫ left.second = right.second := by
        dsimp only [comparison]
        rw [Iso.trans_inv, Iso.symm_inv]
        simp
      have homSecond : comparison.hom ≫ right.second = left.second := by
        rw [← secondSquare, ← Category.assoc, Iso.hom_inv_id,
          Category.id_comp]
      have firstSquare : left.first ≫ comparison.hom = right.first := by
        apply (cancel_mono right.second).mp
        rw [Category.assoc, homSecond, left.composite, right.composite]
      exact
        { midpointIso := comparison
          first_square := firstSquare
          second_square := secondSquare }

theorem preStepFactorizationIso_ext
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    {coAngularFirst : Bool}
    {left right : (preFrobenioid Phi data).PreStepFactorization
      arrow coAngularFirst}
    {first second :
      (preFrobenioid Phi data).PreStepFactorizationIso left right}
    (midpointIso : first.midpointIso = second.midpointIso) :
    first = second := by
  cases first
  cases second
  cases midpointIso
  rfl

theorem preStepFactorizationIso_unique
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    {coAngularFirst : Bool}
    (left right : (preFrobenioid Phi data).PreStepFactorization
      arrow coAngularFirst)
    (first second :
      (preFrobenioid Phi data).PreStepFactorizationIso left right) :
    first = second := by
  have homEquality : first.midpointIso.hom = second.midpointIso.hom := by
    letI : Epi left.first :=
      epi Phi data baseTotallyEpimorphic left.first
    apply (cancel_epi left.first).mp
    exact first.first_square.trans second.first_square.symm
  have isoEquality : first.midpointIso = second.midpointIso := by
    apply Iso.ext
    exact homEquality
  exact preStepFactorizationIso_ext isoEquality

end
end Iut.SourceModelFrobenioid.Carrier
