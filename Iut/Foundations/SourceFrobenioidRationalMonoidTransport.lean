/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Frobenioid

open CategoryTheory

/-!
# Rational-monoid transport in an arbitrary Frobenioid

This file derives the part of Frobenioids I, Proposition 2.2(ii), (iv) used
by the birationalization theorem.  No transport operation is added to the
axioms of a Frobenioid: pullback on `O^triangle` is constructed from the
factorization and universal properties of Definition 1.3.
-/

namespace Iut.FrobenioidRationalMonoidTransport

universe u

noncomputable section

variable (F : FrobenioidPresentation.{u})

/-- Proposition 1.4(i): every arrow out of an isotropic object is
co-angular. -/
theorem isCoAngular_of_isotropicSource
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X) :
    F.preFrobenioid.IsCoAngular arrow := by
  intro U V gamma beta alpha _ _ betaPreStep betaIsometric _
  exact F.axioms.isotropic_closedUnderTargets gamma sourceIsotropic
    beta betaPreStep betaIsometric

/-- Frobenioids I, Proposition 1.9(iv), in the direction not supplied
directly by the target-closure axiom: isotropicity reflects across a
co-angular linear arrow. -/
theorem isIsotropic_source_of_coAngular_linear
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (coAngular : F.preFrobenioid.IsCoAngular arrow)
    (linear : F.preFrobenioid.IsLinear arrow)
    (targetIsotropic : F.preFrobenioid.IsIsotropic Y) :
    F.preFrobenioid.IsIsotropic X := by
  let hull := Classical.choice (F.axioms.isotropicHull X)
  obtain ⟨extension, relation, _⟩ :=
    hull.lift arrow targetIsotropic
  have extensionLinear :
      F.preFrobenioid.IsLinear extension := by
    change F.preFrobenioid.frobeniusDegree extension = 1
    have degrees := congrArg F.preFrobenioid.frobeniusDegree relation
    rw [F.preFrobenioid.frobeniusDegree_comp,
      hull.preStep.1, linear] at degrees
    simpa using degrees
  have hullIso : IsIso hull.hom := by
    apply coAngular (𝟙 X) hull.hom extension
    · simpa only [Category.id_comp] using relation
    · exact extensionLinear
    · exact hull.preStep
    · exact hull.isometric
    · right
      change IsIso (F.preFrobenioid.base.map (𝟙 X))
      infer_instance
  letI : IsIso hull.hom := hullIso
  intro Z f preStep isometric
  exact (F.axioms.isotropic_closedUnderTargets
    (A := hull.hull) (B := X) (inv hull.hom) hull.isotropic)
      f preStep isometric

/-- Frobenioids I, Proposition 1.9(iv): isotropicity is invariant along a
co-angular linear arrow. -/
theorem isIsotropic_source_iff_target_of_coAngular_linear
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (coAngular : F.preFrobenioid.IsCoAngular arrow)
    (linear : F.preFrobenioid.IsLinear arrow) :
    F.preFrobenioid.IsIsotropic X ↔
      F.preFrobenioid.IsIsotropic Y :=
  ⟨F.axioms.isotropic_closedUnderTargets arrow,
    isIsotropic_source_of_coAngular_linear F arrow coAngular linear⟩

/-- Proposition 1.4(iii), directly from the defining co-angular test: an
LB-invertible pre-step is an isomorphism. -/
theorem isIso_of_coAngular_isometric_preStep
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (preStep : F.preFrobenioid.IsPreStep arrow)
    (coAngular : F.preFrobenioid.IsCoAngular arrow)
    (isometric : F.preFrobenioid.IsIsometric arrow) : IsIso arrow := by
  apply coAngular (𝟙 X) arrow (𝟙 Y)
  · simp
  · exact F.preFrobenioid.frobeniusDegree_id Y
  · exact preStep
  · exact isometric
  · left
    change IsIso (F.preFrobenioid.base.map (𝟙 Y))
    infer_instance

/-- A base-isomorphism left factor of a co-angular composite is co-angular
when the right factor is linear.  This is the cancellation step used in
Proposition 1.4(iv). -/
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
        IsIso.of_isIso_comp_right
          (F.preFrobenioid.base.map (gamma ≫ beta))
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
  · simpa only [Category.assoc] using
      congrArg (fun arrow ↦ arrow ≫ second) equality
  · rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      alphaLinear, secondLinear]
    rfl
  · exact betaPreStep
  · exact betaIsometric
  · exact Or.inr gammaBaseIso

/-- Fix a Definition 1.3(iv)(a) factorization for a source arrow.  The final
transport is independent of this choice by its universal equation. -/
private def selectedFactorization
    {X Y : F.carrier} (arrow : X ⟶ Y) :
    F.preFrobenioid.FrobenioidFactorization arrow :=
  Classical.choice (F.axioms.factorization arrow)

private theorem selectedFrobenius_linear
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow) :
    F.preFrobenioid.IsLinear (selectedFactorization F arrow).frobenius := by
  let factorization := selectedFactorization F arrow
  have pullbackLinear :=
    (F.axioms.pullback_linear_lbInvertible factorization.pullback
      factorization.pullback_type).1
  change F.preFrobenioid.frobeniusDegree factorization.frobenius = 1
  have degrees := congrArg F.preFrobenioid.frobeniusDegree
    factorization.composite
  rw [F.preFrobenioid.frobeniusDegree_comp,
    F.preFrobenioid.frobeniusDegree_comp,
    factorization.preStep_type.1, pullbackLinear, linear] at degrees
  simpa using degrees

private theorem selectedPreStep_coAngular
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X) :
    F.preFrobenioid.IsCoAngular
      (selectedFactorization F arrow).preStep := by
  let factorization := selectedFactorization F arrow
  change F.preFrobenioid.IsCoAngular factorization.preStep
  have frobeniusLinear := selectedFrobenius_linear F arrow linear
  have frobeniusPreStep :
      F.preFrobenioid.IsPreStep factorization.frobenius :=
    ⟨frobeniusLinear, factorization.frobenius_type.2⟩
  haveI : IsIso factorization.frobenius :=
    isIso_of_coAngular_isometric_preStep F factorization.frobenius
      frobeniusPreStep factorization.frobenius_type.1.1
      factorization.frobenius_type.1.2
  have firstBaseIso :
      F.preFrobenioid.IsBaseIso
        (factorization.frobenius ≫ factorization.preStep) := by
    change IsIso
      (F.preFrobenioid.base.map
        (factorization.frobenius ≫ factorization.preStep))
    rw [F.preFrobenioid.base.map_comp]
    haveI : IsIso
        (F.preFrobenioid.base.map factorization.frobenius) :=
      factorization.frobenius_type.2
    haveI : IsIso
        (F.preFrobenioid.base.map factorization.preStep) :=
      factorization.preStep_type.2
    infer_instance
  have pullbackLinear :=
    (F.axioms.pullback_linear_lbInvertible factorization.pullback
      factorization.pullback_type).1
  have compositeCoAngular : F.preFrobenioid.IsCoAngular
      ((factorization.frobenius ≫ factorization.preStep) ≫
        factorization.pullback) := by
    rw [Category.assoc, factorization.composite]
    exact isCoAngular_of_isotropicSource F arrow sourceIsotropic
  have firstCoAngular : F.preFrobenioid.IsCoAngular
      (factorization.frobenius ≫ factorization.preStep) :=
    isCoAngular_left_of_comp_linear F
      (factorization.frobenius ≫ factorization.preStep)
      factorization.pullback firstBaseIso pullbackLinear compositeCoAngular
  have midpointIsotropic :
      F.preFrobenioid.IsIsotropic factorization.frobeniusCodomain :=
    F.axioms.isotropic_closedUnderTargets factorization.frobenius
      sourceIsotropic
  have inverseCoAngular : F.preFrobenioid.IsCoAngular
      (inv factorization.frobenius) :=
    isCoAngular_of_isotropicSource F
      (inv factorization.frobenius) midpointIsotropic
  have cancelled : F.preFrobenioid.IsCoAngular
      (inv factorization.frobenius ≫
        (factorization.frobenius ≫ factorization.preStep)) :=
    F.axioms.coAngular_comp
      (inv factorization.frobenius)
      (factorization.frobenius ≫ factorization.preStep)
      inverseCoAngular firstCoAngular
  intro U V gamma beta alpha equality alphaLinear betaPreStep
    betaIsometric baseAlternative
  apply cancelled gamma beta alpha
  · simpa only [IsIso.inv_hom_id_assoc] using equality
  · exact alphaLinear
  · exact betaPreStep
  · exact betaIsometric
  · exact baseAlternative

/-- The comparison target that pulls a base-identity endomorphism through a
pullback arrow. -/
private def pullbackTarget
    {A B : F.carrier} (arrow : A ⟶ B)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism B) :
    F.preFrobenioid.PullbackComparisonTarget arrow A where
  toCodomain := arrow ≫ alpha.hom
  toBaseDomain := 𝟙 _
  commutes := by
    rw [F.preFrobenioid.base.map_comp, alpha.baseIdentity]
    simp

private def pullbackLift
    {A B : F.carrier} (arrow : A ⟶ B)
    (pullback : F.preFrobenioid.IsPullback arrow)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism B) : A ⟶ A :=
  Classical.choose
    ((pullback A).2 (pullbackTarget F arrow alpha))

private theorem pullbackLift_spec
    {A B : F.carrier} (arrow : A ⟶ B)
    (pullback : F.preFrobenioid.IsPullback arrow)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism B) :
    F.preFrobenioid.pullbackComparison arrow A
        (pullbackLift F arrow pullback alpha) =
      pullbackTarget F arrow alpha :=
  Classical.choose_spec
    ((pullback A).2 (pullbackTarget F arrow alpha))

/-- Proposition 1.11(iii): pull an `O^triangle` endomorphism through a
pullback arrow. -/
private def pullbackEndomorphism
    {A B : F.carrier} (arrow : A ⟶ B)
    (pullback : F.preFrobenioid.IsPullback arrow)
    (linear : F.preFrobenioid.IsLinear arrow)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism B) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism A where
  hom := pullbackLift F arrow pullback alpha
  linear := by
    change F.preFrobenioid.frobeniusDegree
        (pullbackLift F arrow pullback alpha) = 1
    have relation := congrArg
      (fun value ↦ value.toCodomain)
      (pullbackLift_spec F arrow pullback alpha)
    change pullbackLift F arrow pullback alpha ≫ arrow =
      arrow ≫ alpha.hom at relation
    have degrees := congrArg F.preFrobenioid.frobeniusDegree relation
    rw [F.preFrobenioid.frobeniusDegree_comp,
      F.preFrobenioid.frobeniusDegree_comp,
      linear, alpha.linear] at degrees
    simpa using degrees
  baseIdentity := by
    have relation := congrArg (fun value ↦ value.toBaseDomain)
      (pullbackLift_spec F arrow pullback alpha)
    change F.preFrobenioid.base.map
      (pullbackLift F arrow pullback alpha) = 𝟙 _ at relation
    exact relation

private theorem pullbackEndomorphism_relation
    {A B : F.carrier} (arrow : A ⟶ B)
    (pullback : F.preFrobenioid.IsPullback arrow)
    (linear : F.preFrobenioid.IsLinear arrow)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism B) :
    (pullbackEndomorphism F arrow pullback linear alpha).hom ≫ arrow =
      arrow ≫ alpha.hom :=
  congrArg (fun value ↦ value.toCodomain)
    (pullbackLift_spec F arrow pullback alpha)

private theorem hom_eq_of_pullback
    {T A B : F.carrier} (arrow : A ⟶ B)
    (pullback : F.preFrobenioid.IsPullback arrow)
    (left right : T ⟶ A)
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

/-- Contravariant transport through a co-angular pre-step is the inverse of
Definition 1.3(iii)(c)'s covariant unit transport. -/
private def preStepPullback
    {A B : F.carrier} (arrow : A ⟶ B)
    (preStep : F.preFrobenioid.IsPreStep arrow)
    (coAngular : F.preFrobenioid.IsCoAngular arrow) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism B ≃*
      F.preFrobenioid.LinearBaseIdentityEndomorphism A :=
  (F.axioms.unitTransport arrow preStep coAngular).transport.symm

private theorem preStepPullback_relation
    {A B : F.carrier} (arrow : A ⟶ B)
    (preStep : F.preFrobenioid.IsPreStep arrow)
    (coAngular : F.preFrobenioid.IsCoAngular arrow)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism B) :
    (preStepPullback F arrow preStep coAngular alpha).hom ≫ arrow =
      arrow ≫ alpha.hom := by
  have relation :=
    (F.axioms.unitTransport arrow preStep coAngular).conjugates
      (preStepPullback F arrow preStep coAngular alpha)
  simpa only [preStepPullback, MulEquiv.apply_symm_apply] using relation

/-- Proposition 1.11(iv), constructed via Definition 1.3(iv)(a): pull through
the final pullback and then through the two co-angular pre-steps. -/
def linearEndomorphismPullback
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism Y) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism X :=
  let factorization := selectedFactorization F arrow
  let pulled := pullbackEndomorphism F factorization.pullback
    factorization.pullback_type
    (F.axioms.pullback_linear_lbInvertible factorization.pullback
      factorization.pullback_type).1 alpha
  let acrossPreStep := preStepPullback F factorization.preStep
    factorization.preStep_type
    (selectedPreStep_coAngular F arrow linear sourceIsotropic) pulled
  preStepPullback F factorization.frobenius
    ⟨selectedFrobenius_linear F arrow linear,
      factorization.frobenius_type.2⟩
    factorization.frobenius_type.1.1 acrossPreStep

theorem linearEndomorphismPullback_relation
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism Y) :
    (linearEndomorphismPullback F arrow linear sourceIsotropic alpha).hom ≫
        arrow =
      arrow ≫ alpha.hom := by
  let factorization := selectedFactorization F arrow
  let pullbackLinear :=
    (F.axioms.pullback_linear_lbInvertible factorization.pullback
      factorization.pullback_type).1
  let pulled := pullbackEndomorphism F factorization.pullback
    factorization.pullback_type pullbackLinear alpha
  let preStepCoAngular : F.preFrobenioid.IsCoAngular factorization.preStep :=
    selectedPreStep_coAngular F arrow linear sourceIsotropic
  let acrossPreStep := preStepPullback F factorization.preStep
    factorization.preStep_type preStepCoAngular pulled
  let frobeniusPreStep :
      F.preFrobenioid.IsPreStep factorization.frobenius :=
    ⟨selectedFrobenius_linear F arrow linear,
      factorization.frobenius_type.2⟩
  have throughPullback := pullbackEndomorphism_relation F
    factorization.pullback factorization.pullback_type pullbackLinear alpha
  have throughPreStep := preStepPullback_relation F
    factorization.preStep factorization.preStep_type preStepCoAngular pulled
  have throughFrobenius := preStepPullback_relation F
    factorization.frobenius frobeniusPreStep
      factorization.frobenius_type.1.1 acrossPreStep
  change pulled.hom ≫ factorization.pullback =
    factorization.pullback ≫ alpha.hom at throughPullback
  change acrossPreStep.hom ≫ factorization.preStep =
    factorization.preStep ≫ pulled.hom at throughPreStep
  change
    (preStepPullback F factorization.frobenius frobeniusPreStep
        factorization.frobenius_type.1.1 acrossPreStep).hom ≫ arrow = _
  calc
    _ = (preStepPullback F factorization.frobenius frobeniusPreStep
          factorization.frobenius_type.1.1 acrossPreStep).hom ≫
        (factorization.frobenius ≫ factorization.preStep ≫
          factorization.pullback) := by
      exact congrArg
        (fun value ↦
          (preStepPullback F factorization.frobenius frobeniusPreStep
            factorization.frobenius_type.1.1 acrossPreStep).hom ≫ value)
        factorization.composite.symm
    _ = factorization.frobenius ≫ acrossPreStep.hom ≫
        factorization.preStep ≫ factorization.pullback := by
      simpa only [Category.assoc] using congrArg
        (fun value ↦ value ≫ factorization.preStep ≫
          factorization.pullback) throughFrobenius
    _ = factorization.frobenius ≫ factorization.preStep ≫
        pulled.hom ≫ factorization.pullback := by
      simpa only [Category.assoc] using congrArg
        (fun value ↦ factorization.frobenius ≫ value ≫
          factorization.pullback) throughPreStep
    _ = factorization.frobenius ≫ factorization.preStep ≫
        factorization.pullback ≫ alpha.hom := by
      simpa only [Category.assoc] using congrArg
        (fun value ↦
          factorization.frobenius ≫ factorization.preStep ≫ value)
        throughPullback
    _ = arrow ≫ alpha.hom := by
      simpa only [Category.assoc] using
        congrArg (fun value ↦ value ≫ alpha.hom)
          factorization.composite

/-- The commuting equation uniquely determines Proposition 1.11(iv)'s
pulled endomorphism. -/
theorem linearEndomorphismPullback_unique
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism Y)
    (candidate : F.preFrobenioid.LinearBaseIdentityEndomorphism X)
    (relation : candidate.hom ≫ arrow = arrow ≫ alpha.hom) :
    candidate =
      linearEndomorphismPullback F arrow linear sourceIsotropic alpha := by
  let factorization := selectedFactorization F arrow
  let pullbackLinear :=
    (F.axioms.pullback_linear_lbInvertible factorization.pullback
      factorization.pullback_type).1
  let pulled := pullbackEndomorphism F factorization.pullback
    factorization.pullback_type pullbackLinear alpha
  let preStepCoAngular : F.preFrobenioid.IsCoAngular factorization.preStep :=
    selectedPreStep_coAngular F arrow linear sourceIsotropic
  let acrossPreStep := preStepPullback F factorization.preStep
    factorization.preStep_type preStepCoAngular pulled
  let frobeniusPreStep :
      F.preFrobenioid.IsPreStep factorization.frobenius :=
    ⟨selectedFrobenius_linear F arrow linear,
      factorization.frobenius_type.2⟩
  let result := linearEndomorphismPullback F arrow linear sourceIsotropic alpha
  have throughPullback := pullbackEndomorphism_relation F
    factorization.pullback factorization.pullback_type pullbackLinear alpha
  have throughPreStep := preStepPullback_relation F
    factorization.preStep factorization.preStep_type preStepCoAngular pulled
  have throughFrobenius := preStepPullback_relation F
    factorization.frobenius frobeniusPreStep
      factorization.frobenius_type.1.1 acrossPreStep
  change pulled.hom ≫ factorization.pullback =
    factorization.pullback ≫ alpha.hom at throughPullback
  change acrossPreStep.hom ≫ factorization.preStep =
    factorization.preStep ≫ pulled.hom at throughPreStep
  have candidateThroughPullback :
      (candidate.hom ≫ factorization.frobenius ≫
          factorization.preStep) ≫ factorization.pullback =
        (factorization.frobenius ≫ factorization.preStep ≫
          pulled.hom) ≫ factorization.pullback := by
    calc
      _ = candidate.hom ≫ arrow := by
        simpa only [Category.assoc] using
          congrArg (fun value ↦ candidate.hom ≫ value)
            factorization.composite
      _ = arrow ≫ alpha.hom := relation
      _ = (factorization.frobenius ≫ factorization.preStep ≫
          factorization.pullback) ≫ alpha.hom := by
        exact congrArg (fun value ↦ value ≫ alpha.hom)
          factorization.composite.symm
      _ = (factorization.frobenius ≫ factorization.preStep ≫
          pulled.hom) ≫ factorization.pullback := by
        simpa only [Category.assoc] using
          congrArg
            (fun value ↦
              (factorization.frobenius ≫ factorization.preStep) ≫ value)
            throughPullback.symm
  have candidateThroughPreStep :
      candidate.hom ≫ factorization.frobenius ≫
          factorization.preStep =
        factorization.frobenius ≫ acrossPreStep.hom ≫
          factorization.preStep := by
    apply hom_eq_of_pullback F factorization.pullback
      factorization.pullback_type
    · calc
        _ = (factorization.frobenius ≫ factorization.preStep ≫
            pulled.hom) ≫ factorization.pullback :=
          candidateThroughPullback
        _ = (factorization.frobenius ≫ acrossPreStep.hom ≫
            factorization.preStep) ≫ factorization.pullback := by
          simpa only [Category.assoc] using
            congrArg (fun value ↦
              factorization.frobenius ≫ value ≫ factorization.pullback)
              throughPreStep.symm
    · have candidateBase := candidate.baseIdentity
      have acrossBase := acrossPreStep.baseIdentity
      change F.preFrobenioid.base.map candidate.hom = 𝟙 _ at candidateBase
      change F.preFrobenioid.base.map acrossPreStep.hom = 𝟙 _ at acrossBase
      simp only [F.preFrobenioid.base.map_comp]
      rw [candidateBase, acrossBase]
      simp
  haveI : Mono factorization.preStep :=
    F.axioms.preStep_mono factorization.preStep
      factorization.preStep_type
  have candidateThroughFrobenius :
      candidate.hom ≫ factorization.frobenius =
        factorization.frobenius ≫ acrossPreStep.hom := by
    apply (cancel_mono factorization.preStep).1
    simpa only [Category.assoc, throughPreStep] using
      candidateThroughPreStep
  haveI : Mono factorization.frobenius :=
    F.axioms.preStep_mono factorization.frobenius frobeniusPreStep
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply (cancel_mono factorization.frobenius).1
  change candidate.hom ≫ factorization.frobenius =
    result.hom ≫ factorization.frobenius
  rw [candidateThroughFrobenius]
  change factorization.frobenius ≫ acrossPreStep.hom =
    (preStepPullback F factorization.frobenius frobeniusPreStep
      factorization.frobenius_type.1.1 acrossPreStep).hom ≫
        factorization.frobenius
  exact throughFrobenius.symm

private theorem linearEndomorphismPullback_one
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X) :
    linearEndomorphismPullback F arrow linear sourceIsotropic 1 = 1 := by
  symm
  apply linearEndomorphismPullback_unique F arrow linear sourceIsotropic 1 1
  change (𝟙 X) ≫ arrow = arrow ≫ (𝟙 Y)
  simp

private theorem linearEndomorphismPullback_mul
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X)
    (left right : F.preFrobenioid.LinearBaseIdentityEndomorphism Y) :
    linearEndomorphismPullback F arrow linear sourceIsotropic (left * right) =
      linearEndomorphismPullback F arrow linear sourceIsotropic left *
        linearEndomorphismPullback F arrow linear sourceIsotropic right := by
  symm
  apply linearEndomorphismPullback_unique F arrow linear sourceIsotropic
    (left * right)
  change
    ((linearEndomorphismPullback F arrow linear sourceIsotropic left).hom ≫
      (linearEndomorphismPullback F arrow linear sourceIsotropic right).hom) ≫
        arrow =
      arrow ≫ (left.hom ≫ right.hom)
  simp only [Category.assoc]
  rw [linearEndomorphismPullback_relation F arrow linear sourceIsotropic right]
  rw [← Category.assoc,
    linearEndomorphismPullback_relation F arrow linear sourceIsotropic left]
  simp only [Category.assoc]

/-- The multiplicative map underlying Proposition 1.11(iv). -/
def linearEndomorphismPullbackHom
    {X Y : F.carrier} (arrow : X ⟶ Y)
    (linear : F.preFrobenioid.IsLinear arrow)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism Y →*
      F.preFrobenioid.LinearBaseIdentityEndomorphism X where
  toFun := linearEndomorphismPullback F arrow linear sourceIsotropic
  map_one' := linearEndomorphismPullback_one F arrow linear sourceIsotropic
  map_mul' := linearEndomorphismPullback_mul F arrow linear sourceIsotropic

theorem linearEndomorphismPullbackHom_id
    (X : F.carrier) (isotropic : F.preFrobenioid.IsIsotropic X) :
    linearEndomorphismPullbackHom F (𝟙 X)
        (F.preFrobenioid.frobeniusDegree_id X) isotropic =
      MonoidHom.id (F.preFrobenioid.LinearBaseIdentityEndomorphism X) := by
  apply MonoidHom.ext
  intro alpha
  symm
  apply linearEndomorphismPullback_unique F (𝟙 X)
    (F.preFrobenioid.frobeniusDegree_id X) isotropic alpha alpha
  simp

theorem linearEndomorphismPullbackHom_comp
    {X Y Z : F.carrier} (first : X ⟶ Y) (second : Y ⟶ Z)
    (firstLinear : F.preFrobenioid.IsLinear first)
    (secondLinear : F.preFrobenioid.IsLinear second)
    (sourceIsotropic : F.preFrobenioid.IsIsotropic X) :
    linearEndomorphismPullbackHom F (first ≫ second) (by
        rw [PreFrobenioid.IsLinear,
          F.preFrobenioid.frobeniusDegree_comp,
          firstLinear, secondLinear]
        rfl) sourceIsotropic =
      (linearEndomorphismPullbackHom F first firstLinear sourceIsotropic).comp
        (linearEndomorphismPullbackHom F second secondLinear
          (F.axioms.isotropic_closedUnderTargets first sourceIsotropic)) := by
  apply MonoidHom.ext
  intro alpha
  symm
  apply linearEndomorphismPullback_unique F (first ≫ second) (by
      rw [PreFrobenioid.IsLinear,
        F.preFrobenioid.frobeniusDegree_comp,
        firstLinear, secondLinear]
      rfl) sourceIsotropic alpha
  change
    (linearEndomorphismPullback F first firstLinear sourceIsotropic
      (linearEndomorphismPullback F second secondLinear
        (F.axioms.isotropic_closedUnderTargets first sourceIsotropic) alpha)).hom ≫
        (first ≫ second) =
      (first ≫ second) ≫ alpha.hom
  rw [← Category.assoc,
    linearEndomorphismPullback_relation F first firstLinear sourceIsotropic]
  rw [Category.assoc,
    linearEndomorphismPullback_relation F second secondLinear]
  simp only [Category.assoc]

/-- Extend a rational endomorphism across an isotropic hull by its universal
property, as in Proposition 2.2(iv). -/
private def hullExtension
    (A : F.carrier) (hull : F.preFrobenioid.IsotropicHull A)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism A) :
    hull.hull ⟶ hull.hull :=
  Classical.choose (hull.lift (alpha.hom ≫ hull.hom) hull.isotropic)

private theorem hullExtension_spec
    (A : F.carrier) (hull : F.preFrobenioid.IsotropicHull A)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism A) :
    hull.hom ≫ hullExtension F A hull alpha =
      alpha.hom ≫ hull.hom :=
  (Classical.choose_spec
    (hull.lift (alpha.hom ≫ hull.hom) hull.isotropic)).1

private def hullEndomorphism
    (A : F.carrier) (hull : F.preFrobenioid.IsotropicHull A)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism A) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism hull.hull where
  hom := hullExtension F A hull alpha
  linear := by
    change F.preFrobenioid.frobeniusDegree
      (hullExtension F A hull alpha) = 1
    have degrees := congrArg F.preFrobenioid.frobeniusDegree
      (hullExtension_spec F A hull alpha)
    rw [F.preFrobenioid.frobeniusDegree_comp,
      F.preFrobenioid.frobeniusDegree_comp,
      hull.preStep.1, alpha.linear] at degrees
    simpa using degrees
  baseIdentity := by
    change F.preFrobenioid.base.map (hullExtension F A hull alpha) = 𝟙 _
    have baseEquation := congrArg F.preFrobenioid.base.map
      (hullExtension_spec F A hull alpha)
    rw [F.preFrobenioid.base.map_comp,
      F.preFrobenioid.base.map_comp, alpha.baseIdentity] at baseEquation
    haveI : Epi (F.preFrobenioid.base.map hull.hom) :=
      F.baseTotallyEpimorphic (F.preFrobenioid.base.map hull.hom)
    apply (cancel_epi (F.preFrobenioid.base.map hull.hom)).1
    simpa using baseEquation

private theorem hullEndomorphism_unique
    (A : F.carrier) (hull : F.preFrobenioid.IsotropicHull A)
    (alpha : F.preFrobenioid.LinearBaseIdentityEndomorphism A)
    (candidate :
      F.preFrobenioid.LinearBaseIdentityEndomorphism hull.hull)
    (relation : hull.hom ≫ candidate.hom = alpha.hom ≫ hull.hom) :
    candidate = hullEndomorphism F A hull alpha := by
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  exact (Classical.choose_spec
    (hull.lift (alpha.hom ≫ hull.hom) hull.isotropic)).2
      candidate.hom relation

private theorem hullEndomorphism_one
    (A : F.carrier) (hull : F.preFrobenioid.IsotropicHull A) :
    hullEndomorphism F A hull 1 = 1 := by
  symm
  apply hullEndomorphism_unique F A hull 1 1
  change hull.hom ≫ (𝟙 hull.hull) = (𝟙 A) ≫ hull.hom
  simp

private theorem hullEndomorphism_mul
    (A : F.carrier) (hull : F.preFrobenioid.IsotropicHull A)
    (left right : F.preFrobenioid.LinearBaseIdentityEndomorphism A) :
    hullEndomorphism F A hull (left * right) =
      hullEndomorphism F A hull left * hullEndomorphism F A hull right := by
  symm
  apply hullEndomorphism_unique F A hull (left * right)
  change hull.hom ≫
      (hullExtension F A hull left ≫
        hullExtension F A hull right) =
    (left.hom ≫ right.hom) ≫ hull.hom
  rw [← Category.assoc, hullExtension_spec F A hull left]
  rw [Category.assoc, hullExtension_spec F A hull right]
  simp only [Category.assoc]

private def hullInclusion
    (A : F.carrier) (hull : F.preFrobenioid.IsotropicHull A) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism A →*
      F.preFrobenioid.LinearBaseIdentityEndomorphism hull.hull where
  toFun := hullEndomorphism F A hull
  map_one' := hullEndomorphism_one F A hull
  map_mul' := hullEndomorphism_mul F A hull

private theorem hullInclusion_injective
    (A : F.carrier) (hull : F.preFrobenioid.IsotropicHull A) :
    Function.Injective (hullInclusion F A hull) := by
  intro left right equality
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  haveI : Mono hull.hom :=
    F.axioms.preStep_mono hull.hom hull.preStep
  apply (cancel_mono hull.hom).1
  rw [← hullExtension_spec F A hull left,
    ← hullExtension_spec F A hull right]
  exact congrArg (fun value ↦ hull.hom ≫ value.hom) equality

/-- Frobenioids I, Proposition 2.2(ii), (iv), for an arbitrary
`FrobenioidPresentation`. -/
def rationalMonoidTransport :
    F.preFrobenioid.RationalMonoidTransport where
  pullback {X Y} f :=
    linearEndomorphismPullbackHom F f.hom f.linear X.isotropic
  pullback_id X := by
    simpa only [PreFrobenioid.isotropicLinear_id_hom] using
      linearEndomorphismPullbackHom_id F X.obj X.isotropic
  pullback_comp {X Y Z} f g := by
    simpa only [PreFrobenioid.isotropicLinear_comp_hom] using
      linearEndomorphismPullbackHom_comp F f.hom g.hom f.linear g.linear
        X.isotropic
  hullInclusion A hull := hullInclusion F A hull
  hullInclusion_injective A hull := hullInclusion_injective F A hull

end

end Iut.FrobenioidRationalMonoidTransport
