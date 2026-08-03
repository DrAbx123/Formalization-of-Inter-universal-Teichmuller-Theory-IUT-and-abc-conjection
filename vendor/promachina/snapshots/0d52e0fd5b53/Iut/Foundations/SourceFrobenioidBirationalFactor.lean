/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidBirationalAxioms
import Mathlib.Tactic.Abel

/-!
# The restricted divisor factor of generic birationalization

This file completes the factorization in the corrected form of Frobenioids I,
Proposition 4.4(iii).  The functor of Proposition 4.4(i) is not expected to
factor strictly without first choosing its objectwise 1-isomorphism: even in
the explicit model its raw divisor coordinate contains object-class terms.
We therefore construct the source's literal 1-factorization.  An objectwise
potential normalizes those terms, the normalized functor lands strictly in
`F_(Phi^birat)`, and its composite with the subgroup inclusion is naturally
isomorphic to the original groupified functor.

The potential is canonical up to a rational-function divisor.  On an
isotropic object it is the negative divisor of a chosen degree-two,
base-identity endomorphism.  An arbitrary object inherits its potential from
its isotropic hull.  Frobenius normalization is used exactly where the paper's
official correction (29) requires it: to prove that every normalized arrow
divisor lies in `Phi^birat`.
-/

open CategoryTheory

namespace Iut.FrobenioidBirationalization

universe u

noncomputable section

variable (F : FrobenioidPresentation.{u})

/-- The raw external divisor of the Proposition 4.4(i) functor, expressed
against the target pre-Frobenioid's definitionally equal base object. -/
def birationalRawDivisor
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj
        ((preFrobenioid F).base.obj source)).carrier := by
  exact ((groupifiedBirationalFunctor F).map arrow).divisor

/-- The object potential on an isotropic target object: minus the external
`Phi^gp` divisor of a degree-two base-identity endomorphism. -/
def birationalIsotropicPotential
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) :
    Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj
        ((preFrobenioid F).base.obj object)).carrier :=
  -birationalRawDivisor F
    (birationalIsotropicDegreeTwoEndomorphism F object isotropic)

/-- The identity isotropic hull used when an object is already isotropic. -/
def birationalIdentityIsotropicHull
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) :
    (preFrobenioid F).IsotropicHull object where
  hull := object
  hom := 𝟙 object
  preStep := by
    exact (birational_isPreStep_of_isIso F (𝟙 object) inferInstance)
  isometric := isIsometric F (𝟙 object)
  isotropic := isotropic
  lift {target} arrow _ := by
    refine ⟨arrow, by simp, ?_⟩
    intro candidate equality
    simpa using equality

/-- A chosen isotropic gauge: identity on an isotropic object, otherwise the
generic isotropic hull. -/
def birationalIsotropicGauge (object : BirationalCategory F) :
    (preFrobenioid F).IsotropicHull object :=
  @dite _ ((preFrobenioid F).IsIsotropic object)
    (Classical.propDecidable _)
    (fun isotropic => birationalIdentityIsotropicHull F object isotropic)
    (fun _ => birational_isotropicHull F object)

/-- The chosen gauge is definitionally the identity hull on an isotropic
object.  Isolating the dependent conditional here keeps later transport
proofs independent of its implementation. -/
theorem birationalIsotropicGauge_eq_identity
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) :
    birationalIsotropicGauge F object =
      birationalIdentityIsotropicHull F object isotropic := by
  classical
  simp [birationalIsotropicGauge, isotropic]

/-- The object potential on an arbitrary target object, transported back from
its isotropic hull and corrected by the hull arrow's raw divisor. -/
def birationalObjectPotential (object : BirationalCategory F) :
    Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj
        ((preFrobenioid F).base.obj object)).carrier :=
  @dite _ ((preFrobenioid F).IsIsotropic object)
      (Classical.propDecidable _) (fun isotropic =>
        birationalIsotropicPotential F object isotropic) (fun _ =>
        let hull := birational_isotropicHull F object
        F.preFrobenioid.divisorMonoid.gpPullback
            ((preFrobenioid F).base.map hull.hom)
            (birationalIsotropicPotential F hull.hull hull.isotropic) -
          birationalRawDivisor F hull.hom)

/-- On an isotropic object the general potential is the isotropic potential. -/
theorem birationalObjectPotential_of_isotropic
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) :
    birationalObjectPotential F object =
      birationalIsotropicPotential F object isotropic := by
  simp [birationalObjectPotential, isotropic]

/-- The divisor coordinate after conjugating the groupified functor by the
object potentials. -/
def birationalNormalizedDivisor
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    Algebra.GrothendieckAddGroup
      (F.preFrobenioid.divisorMonoid.obj
        ((preFrobenioid F).base.obj source)).carrier :=
  birationalRawDivisor F arrow +
      ((preFrobenioid F).frobeniusDegree arrow).1 •
        birationalObjectPotential F source -
    F.preFrobenioid.divisorMonoid.gpPullback
      ((preFrobenioid F).base.map arrow)
      (birationalObjectPotential F target)

/-- Normalized divisors obey the elementary-Frobenioid composition law. -/
theorem birationalNormalizedDivisor_comp
    {source middle target : BirationalCategory F}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    birationalNormalizedDivisor F (first ≫ second) =
      F.preFrobenioid.divisorMonoid.gpPullback
          ((preFrobenioid F).base.map first)
          (birationalNormalizedDivisor F second) +
        ((preFrobenioid F).frobeniusDegree second).1 •
          birationalNormalizedDivisor F first := by
  rw [birationalNormalizedDivisor, birationalNormalizedDivisor,
    birationalNormalizedDivisor, birationalRawDivisor,
    birationalRawDivisor, birationalRawDivisor,
    (groupifiedBirationalFunctor F).map_comp,
    (preFrobenioid F).base.map_comp,
    (preFrobenioid F).frobeniusDegree_comp]
  change
    (F.preFrobenioid.divisorMonoid.gpPullback
          ((groupifiedBirationalFunctor F).map first).base
          ((groupifiedBirationalFunctor F).map second).divisor +
        ((groupifiedBirationalFunctor F).map second).frobeniusDegree.1 •
          ((groupifiedBirationalFunctor F).map first).divisor) +
        _ - _ = _
  rw [
    groupifiedBirationalFunctor_map_base,
    groupifiedBirationalFunctor_map_frobeniusDegree,
    F.preFrobenioid.divisorMonoid.gpPullback_comp]
  have degreeVal :
      ((preFrobenioid F).frobeniusDegree first *
        (preFrobenioid F).frobeniusDegree second).1 =
      ((preFrobenioid F).frobeniusDegree first).1 *
        ((preFrobenioid F).frobeniusDegree second).1 := rfl
  rw [degreeVal, mul_nsmul]
  simp only [AddMonoidHom.comp_apply, map_add, map_sub, map_nsmul,
    nsmul_add, nsmul_sub]
  simp only [sub_eq_add_neg]
  abel_nf
  ac_rfl

/-- The normalized divisor of an identity is zero. -/
theorem birationalNormalizedDivisor_id (object : BirationalCategory F) :
    birationalNormalizedDivisor F (𝟙 object) = 0 := by
  rw [birationalNormalizedDivisor, birationalRawDivisor,
    (groupifiedBirationalFunctor F).map_id,
    (preFrobenioid F).frobeniusDegree_id,
    (preFrobenioid F).base.map_id,
    F.preFrobenioid.divisorMonoid.gpPullback_id]
  change 0 + (1 : ℕ) • birationalObjectPotential F object -
      AddMonoidHom.id _ (birationalObjectPotential F object) = 0
  rw [zero_add, one_nsmul, AddMonoidHom.id_apply, sub_self]

/-- A linear base-identity endomorphism is not changed by potential
normalization. -/
theorem birationalNormalizedDivisor_linearBaseIdentity
    {object : BirationalCategory F}
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism object) :
    birationalNormalizedDivisor F value.hom =
      birationalRawDivisor F value.hom := by
  rw [birationalNormalizedDivisor, value.linear, value.baseIdentity,
    F.preFrobenioid.divisorMonoid.gpPullback_id]
  change _ + (1 : ℕ) • birationalObjectPotential F object -
      AddMonoidHom.id _ (birationalObjectPotential F object) = _
  rw [one_nsmul, AddMonoidHom.id_apply, add_sub_cancel_right]

/-- On an isotropic object, the selected degree-two endomorphism has zero
divisor after normalization by the corresponding isotropic potential. -/
theorem birationalIsotropicPotential_normalizes_degreeTwo
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) :
    birationalRawDivisor F
          (birationalIsotropicDegreeTwoEndomorphism F object isotropic) +
        (2 : ℕ) • birationalIsotropicPotential F object isotropic -
      F.preFrobenioid.divisorMonoid.gpPullback (𝟙 _)
        (birationalIsotropicPotential F object isotropic) = 0 := by
  rw [birationalIsotropicPotential,
    F.preFrobenioid.divisorMonoid.gpPullback_id]
  change _ + (2 : ℕ) • (-_) - AddMonoidHom.id _ (-_) = 0
  rw [AddMonoidHom.id_apply]
  abel

/-- The selected degree-two endomorphism of an isotropic object has zero
normalized divisor. -/
theorem birationalNormalizedDivisor_degreeTwo_of_isotropic
    (object : BirationalCategory F)
    (isotropic : (preFrobenioid F).IsIsotropic object) :
    birationalNormalizedDivisor F
      (birationalIsotropicDegreeTwoEndomorphism F object isotropic) = 0 := by
  rw [birationalNormalizedDivisor,
    birationalObjectPotential_of_isotropic F object isotropic,
    birationalIsotropicDegreeTwoEndomorphism_degree F object isotropic,
    birationalIsotropicDegreeTwoEndomorphism_baseIdentity F object isotropic]
  exact birationalIsotropicPotential_normalizes_degreeTwo F object isotropic

/-- A rational function on an isotropic target represents an element of the
base-indexed birational divisor range. -/
theorem birationalRawDivisor_mem_baseRange_of_isotropic
    {object : BirationalCategory F}
    (isotropic : (preFrobenioid F).IsIsotropic object)
    (value : (preFrobenioid F).LinearBaseIdentityEndomorphism object) :
    birationalRawDivisor F value.hom ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj object) := by
  rcases object with ⟨⟨sourceObject⟩⟩
  let representative := birationalIsotropicBaseRepresentative F
    (F.preFrobenioid.base.obj sourceObject)
  obtain ⟨comparison, comparisonBase⟩ :=
    birational_iso_over_baseIso_of_isotropic F
      ((localizationFunctor F).obj representative.object)
      ((localizationFunctor F).obj sourceObject)
      representative.isotropic isotropic representative.baseIso
  have objectMembership : birationalRawDivisor F value.hom ∈
      birationalDivisorRange F sourceObject := by
    apply (mem_birationalDivisorRange_iff F sourceObject _).2
    exact ⟨value, rfl⟩
  have transported :=
    (gpPullback_mem_birationalDivisorRange_iff_of_isIso F comparison.hom
      (birationalRawDivisor F value.hom)).2 objectMembership
  apply (mem_birationalBaseDivisorRange_iff F
    (F.preFrobenioid.base.obj sourceObject) _).2
  rw [← comparisonBase]
  exact transported

/-- Essential uniqueness compares parallel Frobenius-type arrows of the same
degree by a target automorphism. -/
structure BirationalParallelFrobeniusComparison
    {source target : BirationalCategory F} (left right : source ⟶ target) where
  iso : target ≅ target
  square : left ≫ iso.hom = right

/-- The comparison automorphism supplied by the target Frobenius-degree
witness. -/
def birationalParallelFrobeniusComparison
    {source target : BirationalCategory F} (left right : source ⟶ target)
    (leftType : (preFrobenioid F).IsOfFrobeniusType left)
    (rightType : (preFrobenioid F).IsOfFrobeniusType right)
    (degreeEquality : (preFrobenioid F).frobeniusDegree left =
      (preFrobenioid F).frobeniusDegree right) :
    BirationalParallelFrobeniusComparison F left right := by
  let witness := birational_frobeniusDegree F source
    ((preFrobenioid F).frobeniusDegree left)
  let leftExistence := witness.essentiallyUnique left leftType rfl
  let leftIso := Classical.choose leftExistence
  have leftSquare : witness.hom ≫ leftIso.hom = left :=
    (Classical.choose_spec leftExistence).1
  let rightExistence := witness.essentiallyUnique right rightType
    degreeEquality.symm
  let rightIso := Classical.choose rightExistence
  have rightSquare : witness.hom ≫ rightIso.hom = right :=
    (Classical.choose_spec rightExistence).1
  let comparison := leftIso.symm ≪≫ rightIso
  refine ⟨comparison, ?_⟩
  dsimp only [comparison]
  rw [Iso.trans_hom, Iso.symm_hom]
  calc
    left ≫ leftIso.inv ≫ rightIso.hom =
        (witness.hom ≫ leftIso.hom) ≫ leftIso.inv ≫ rightIso.hom := by
      exact congrArg (fun arrow ↦ arrow ≫ leftIso.inv ≫ rightIso.hom)
        leftSquare.symm
    _ = witness.hom ≫ rightIso.hom := by simp
    _ = right := rightSquare

/-- A Frobenius-type arrow between isotropic objects has normalized divisor
in the birational range.  The proof compares the selected degree-two
endomorphisms across the arrow and reads the comparison automorphism as the
required rational function. -/
theorem birationalNormalizedDivisor_mem_of_frobeniusType
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (arrowType : (preFrobenioid F).IsOfFrobeniusType arrow)
    (sourceIsotropic : (preFrobenioid F).IsIsotropic source) :
    birationalNormalizedDivisor F arrow ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj source) := by
  let targetIsotropic : (preFrobenioid F).IsIsotropic target :=
    birational_isotropic_closedUnderTargets F arrow sourceIsotropic
  letI : IsIso ((preFrobenioid F).base.map arrow) := arrowType.2
  let sourcePhi :=
    birationalIsotropicDegreeTwoEndomorphism F source sourceIsotropic
  let targetPhi :=
    birationalIsotropicDegreeTwoEndomorphism F target targetIsotropic
  let left := sourcePhi ≫ arrow
  let right := arrow ≫ targetPhi
  have leftType : (preFrobenioid F).IsOfFrobeniusType left := by
    refine ⟨⟨birational_isCoAngular_of_isotropicSource F left
      sourceIsotropic, isGroupLikeType F source
        ((preFrobenioid F).divisor left)⟩, ?_⟩
    change IsIso ((preFrobenioid F).base.map left)
    dsimp only [left]
    rw [(preFrobenioid F).base.map_comp,
      birationalIsotropicDegreeTwoEndomorphism_baseIdentity F source
        sourceIsotropic]
    infer_instance
  have rightType : (preFrobenioid F).IsOfFrobeniusType right := by
    refine ⟨⟨birational_isCoAngular_of_isotropicSource F right
      sourceIsotropic, isGroupLikeType F source
        ((preFrobenioid F).divisor right)⟩, ?_⟩
    change IsIso ((preFrobenioid F).base.map right)
    dsimp only [right]
    rw [(preFrobenioid F).base.map_comp,
      birationalIsotropicDegreeTwoEndomorphism_baseIdentity F target
        targetIsotropic]
    infer_instance
  have degreeEquality : (preFrobenioid F).frobeniusDegree left =
      (preFrobenioid F).frobeniusDegree right := by
    dsimp only [left, right, sourcePhi, targetPhi]
    rw [(preFrobenioid F).frobeniusDegree_comp,
      (preFrobenioid F).frobeniusDegree_comp,
      birationalIsotropicDegreeTwoEndomorphism_degree F source
        sourceIsotropic,
      birationalIsotropicDegreeTwoEndomorphism_degree F target
        targetIsotropic]
    exact mul_comm _ _
  let comparison := birationalParallelFrobeniusComparison F left right
    leftType rightType degreeEquality
  let correction :
      (preFrobenioid F).LinearBaseIdentityEndomorphism target :=
    { hom := comparison.iso.hom
      linear := (birational_isPreStep_of_isIso F comparison.iso.hom
        (by infer_instance)).1
      baseIdentity := by
        have mappedSquare := congrArg (preFrobenioid F).base.map
          comparison.square
        have leftBase : (preFrobenioid F).base.map left =
            (preFrobenioid F).base.map arrow := by
          dsimp only [left, sourcePhi]
          rw [(preFrobenioid F).base.map_comp,
            birationalIsotropicDegreeTwoEndomorphism_baseIdentity F source
              sourceIsotropic, Category.id_comp]
        have rightBase : (preFrobenioid F).base.map right =
            (preFrobenioid F).base.map arrow := by
          dsimp only [right, targetPhi]
          rw [(preFrobenioid F).base.map_comp,
            birationalIsotropicDegreeTwoEndomorphism_baseIdentity F target
              targetIsotropic, Category.comp_id]
        rw [(preFrobenioid F).base.map_comp, leftBase, rightBase]
          at mappedSquare
        letI : Epi ((preFrobenioid F).base.map arrow) :=
          F.baseTotallyEpimorphic _
        apply (cancel_epi ((preFrobenioid F).base.map arrow)).1
        simpa using mappedSquare }
  have correctionMem : birationalRawDivisor F correction.hom ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj target) :=
    birationalRawDivisor_mem_baseRange_of_isotropic F targetIsotropic
      correction
  have normalizedSquare := congrArg (birationalNormalizedDivisor F)
    comparison.square
  have sourcePhiZero : birationalNormalizedDivisor F sourcePhi = 0 :=
    birationalNormalizedDivisor_degreeTwo_of_isotropic F source
      sourceIsotropic
  have targetPhiZero : birationalNormalizedDivisor F targetPhi = 0 :=
    birationalNormalizedDivisor_degreeTwo_of_isotropic F target
      targetIsotropic
  have correctionNormalized : birationalNormalizedDivisor F correction.hom =
      birationalRawDivisor F correction.hom :=
    birationalNormalizedDivisor_linearBaseIdentity F correction
  have divisorEquality : birationalNormalizedDivisor F arrow =
      F.preFrobenioid.divisorMonoid.gpPullback
        ((preFrobenioid F).base.map arrow)
        (birationalRawDivisor F correction.hom) := by
    rw [birationalNormalizedDivisor_comp,
      birationalNormalizedDivisor_comp] at normalizedSquare
    dsimp only [left, right, sourcePhi, targetPhi] at normalizedSquare
    rw [birationalNormalizedDivisor_comp,
      sourcePhiZero, targetPhiZero, correctionNormalized,
      birationalIsotropicDegreeTwoEndomorphism_baseIdentity F source
        sourceIsotropic,
      F.preFrobenioid.divisorMonoid.gpPullback_id,
      birationalIsotropicDegreeTwoEndomorphism_degree F target
        targetIsotropic,
      correction.linear] at normalizedSquare
    rw [(preFrobenioid F).base.map_comp,
      birationalIsotropicDegreeTwoEndomorphism_baseIdentity F source
        sourceIsotropic, Category.id_comp] at normalizedSquare
    simp only [AddMonoidHom.id_apply, nsmul_zero, add_zero, map_zero,
      zero_add] at normalizedSquare
    change _ + (1 : ℕ) • birationalNormalizedDivisor F arrow =
      (2 : ℕ) • birationalNormalizedDivisor F arrow at normalizedSquare
    rw [one_nsmul, two_nsmul] at normalizedSquare
    exact (add_right_cancel normalizedSquare).symm
  rw [divisorEquality]
  exact gpPullback_mem_birationalBaseDivisorRange F
    ((preFrobenioid F).base.map arrow) correctionMem

/-- Pull a base-identity Frobenius endomorphism through a pullback arrow.
The universal property determines both the commuting square and the exact
base coordinate of the lift. -/
structure BirationalFrobeniusPullback
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (targetPhi : target ⟶ target) where
  hom : source ⟶ source
  relation : hom ≫ arrow = arrow ≫ targetPhi
  baseIdentity : (preFrobenioid F).IsBaseIdentity hom
  degree : (preFrobenioid F).frobeniusDegree hom =
    (preFrobenioid F).frobeniusDegree targetPhi

/-- The Frobenius pullback obtained from the representable pullback
comparison. -/
def birationalFrobeniusPullback
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (pullback : (preFrobenioid F).IsPullback arrow)
    (targetPhi : target ⟶ target)
    (targetBaseIdentity : (preFrobenioid F).IsBaseIdentity targetPhi) :
    BirationalFrobeniusPullback F arrow targetPhi := by
  let comparison : (preFrobenioid F).PullbackComparisonTarget arrow source :=
    { toCodomain := arrow ≫ targetPhi
      toBaseDomain := 𝟙 _
      commutes := by
        rw [(preFrobenioid F).base.map_comp, targetBaseIdentity]
        simp }
  let lift := Classical.choose ((pullback source).2 comparison)
  have liftComparison := Classical.choose_spec
    ((pullback source).2 comparison)
  have relation := congrArg
    PreFrobenioid.PullbackComparisonTarget.toCodomain liftComparison
  have baseIdentity := congrArg
    PreFrobenioid.PullbackComparisonTarget.toBaseDomain liftComparison
  refine ⟨lift, ?_, baseIdentity, ?_⟩
  · exact relation
  · change lift ≫ arrow = arrow ≫ targetPhi at relation
    have degrees := congrArg (preFrobenioid F).frobeniusDegree relation
    rw [(preFrobenioid F).frobeniusDegree_comp,
      (preFrobenioid F).frobeniusDegree_comp,
      (birational_pullback_linear_lbInvertible F arrow pullback).1]
      at degrees
    simpa using degrees

/-- A pullback arrow between isotropic objects has normalized divisor in the
birational range. -/
theorem birationalNormalizedDivisor_mem_of_pullback
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (pullback : (preFrobenioid F).IsPullback arrow)
    (sourceIsotropic : (preFrobenioid F).IsIsotropic source)
    (targetIsotropic : (preFrobenioid F).IsIsotropic target) :
    birationalNormalizedDivisor F arrow ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj source) := by
  let sourcePhi :=
    birationalIsotropicDegreeTwoEndomorphism F source sourceIsotropic
  let targetPhi :=
    birationalIsotropicDegreeTwoEndomorphism F target targetIsotropic
  let lifted := birationalFrobeniusPullback F arrow pullback targetPhi
    (birationalIsotropicDegreeTwoEndomorphism_baseIdentity F target
      targetIsotropic)
  have sourcePhiType : (preFrobenioid F).IsOfFrobeniusType sourcePhi := by
    refine ⟨⟨birational_isCoAngular_of_isotropicSource F sourcePhi
      sourceIsotropic, isGroupLikeType F source
        ((preFrobenioid F).divisor sourcePhi)⟩, ?_⟩
    change IsIso ((preFrobenioid F).base.map sourcePhi)
    dsimp only [sourcePhi]
    rw [birationalIsotropicDegreeTwoEndomorphism_baseIdentity F source
      sourceIsotropic]
    infer_instance
  have liftedType : (preFrobenioid F).IsOfFrobeniusType lifted.hom := by
    refine ⟨⟨birational_isCoAngular_of_isotropicSource F lifted.hom
      sourceIsotropic, isGroupLikeType F source
        ((preFrobenioid F).divisor lifted.hom)⟩, ?_⟩
    change IsIso ((preFrobenioid F).base.map lifted.hom)
    rw [lifted.baseIdentity]
    infer_instance
  have degreeEquality : (preFrobenioid F).frobeniusDegree sourcePhi =
      (preFrobenioid F).frobeniusDegree lifted.hom := by
    rw [birationalIsotropicDegreeTwoEndomorphism_degree F source
      sourceIsotropic, lifted.degree,
      birationalIsotropicDegreeTwoEndomorphism_degree F target
        targetIsotropic]
  let comparison := birationalParallelFrobeniusComparison F sourcePhi
    lifted.hom sourcePhiType liftedType degreeEquality
  let correction :
      (preFrobenioid F).LinearBaseIdentityEndomorphism source :=
    { hom := comparison.iso.hom
      linear := (birational_isPreStep_of_isIso F comparison.iso.hom
        (by infer_instance)).1
      baseIdentity := by
        have mappedSquare := congrArg (preFrobenioid F).base.map
          comparison.square
        rw [(preFrobenioid F).base.map_comp,
          birationalIsotropicDegreeTwoEndomorphism_baseIdentity F source
            sourceIsotropic,
          lifted.baseIdentity, Category.id_comp] at mappedSquare
        exact mappedSquare }
  have correctionMem : birationalRawDivisor F correction.hom ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj source) :=
    birationalRawDivisor_mem_baseRange_of_isotropic F sourceIsotropic
      correction
  have sourcePhiZero : birationalNormalizedDivisor F sourcePhi = 0 :=
    birationalNormalizedDivisor_degreeTwo_of_isotropic F source
      sourceIsotropic
  have targetPhiZero : birationalNormalizedDivisor F targetPhi = 0 :=
    birationalNormalizedDivisor_degreeTwo_of_isotropic F target
      targetIsotropic
  have correctionNormalized : birationalNormalizedDivisor F correction.hom =
      birationalRawDivisor F correction.hom :=
    birationalNormalizedDivisor_linearBaseIdentity F correction
  have liftedNormalized : birationalNormalizedDivisor F lifted.hom =
      birationalRawDivisor F correction.hom := by
    have normalizedSquare := congrArg (birationalNormalizedDivisor F)
      comparison.square
    rw [birationalNormalizedDivisor_comp,
      sourcePhiZero, correctionNormalized,
      birationalIsotropicDegreeTwoEndomorphism_baseIdentity F source
        sourceIsotropic,
      F.preFrobenioid.divisorMonoid.gpPullback_id,
      correction.linear] at normalizedSquare
    simpa using normalizedSquare.symm
  have relationNormalized := congrArg (birationalNormalizedDivisor F)
    lifted.relation
  have arrowLinear := (birational_pullback_linear_lbInvertible F arrow
    pullback).1
  rw [birationalNormalizedDivisor_comp,
    birationalNormalizedDivisor_comp, liftedNormalized, targetPhiZero,
    lifted.baseIdentity,
    F.preFrobenioid.divisorMonoid.gpPullback_id,
    arrowLinear,
    birationalIsotropicDegreeTwoEndomorphism_degree F target
      targetIsotropic] at relationNormalized
  have divisorEquality : birationalNormalizedDivisor F arrow =
      birationalRawDivisor F correction.hom := by
    simp only [AddMonoidHom.id_apply, map_zero, zero_add]
      at relationNormalized
    change birationalNormalizedDivisor F arrow +
        (1 : ℕ) • birationalRawDivisor F correction.hom =
      (2 : ℕ) • birationalNormalizedDivisor F arrow at relationNormalized
    rw [one_nsmul, two_nsmul] at relationNormalized
    exact (add_left_cancel relationNormalized).symm
  rw [divisorEquality]
  exact correctionMem

/-- The chosen isotropic-gauge arrow has zero normalized divisor by
construction. -/
theorem birationalNormalizedDivisor_isotropicGauge
    (object : BirationalCategory F) :
    birationalNormalizedDivisor F
      (birationalIsotropicGauge F object).hom = 0 := by
  classical
  by_cases isotropic : (preFrobenioid F).IsIsotropic object
  · rw [birationalIsotropicGauge_eq_identity F object isotropic]
    exact birationalNormalizedDivisor_id F object
  · let hull := birational_isotropicHull F object
    have gaugeEq : birationalIsotropicGauge F object = hull := by
      simp [birationalIsotropicGauge, isotropic, hull]
    have potentialEq : birationalObjectPotential F object =
        F.preFrobenioid.divisorMonoid.gpPullback
            ((preFrobenioid F).base.map hull.hom)
            (birationalIsotropicPotential F hull.hull hull.isotropic) -
          birationalRawDivisor F hull.hom := by
      simp [birationalObjectPotential, isotropic, hull]
    rw [birationalNormalizedDivisor]
    rw [gaugeEq, potentialEq]
    rw [birationalObjectPotential_of_isotropic F hull.hull hull.isotropic]
    rw [hull.preStep.1]
    change _ + (1 : ℕ) • (_ - _) - _ = 0
    rw [one_nsmul]
    abel

/-- Membership of normalized divisors is closed under composition. -/
theorem birationalNormalizedDivisor_mem_comp
    {source middle target : BirationalCategory F}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstMem : birationalNormalizedDivisor F first ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj source))
    (secondMem : birationalNormalizedDivisor F second ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj middle)) :
    birationalNormalizedDivisor F (first ≫ second) ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj source) := by
  rw [birationalNormalizedDivisor_comp]
  exact AddSubgroup.add_mem _
    (gpPullback_mem_birationalBaseDivisorRange F
      ((preFrobenioid F).base.map first) secondMem)
    (AddSubgroup.nsmul_mem _ firstMem _)

set_option maxHeartbeats 800000 in
-- The dependent three-stage factorization requires deeper elaboration than the default.
/-- Every arrow between isotropic objects has normalized divisor in the
birational range.  This is the three-stage Frobenius/pre-step/pullback
factorization, with the pre-step treated as a pullback because isotropicity
makes it an isomorphism. -/
theorem birationalNormalizedDivisor_mem_of_isotropic
    {source target : BirationalCategory F} (arrow : source ⟶ target)
    (sourceIsotropic : (preFrobenioid F).IsIsotropic source)
    (targetIsotropic : (preFrobenioid F).IsIsotropic target) :
    birationalNormalizedDivisor F arrow ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj source) := by
  let factor := Classical.choice (birational_factorization F arrow)
  have frobeniusCodomainIsotropic :
      (preFrobenioid F).IsIsotropic factor.frobeniusCodomain :=
    birational_isotropic_closedUnderTargets F factor.frobenius
      sourceIsotropic
  have preStepCodomainIsotropic :
      (preFrobenioid F).IsIsotropic factor.preStepCodomain :=
    birational_isotropic_closedUnderTargets F factor.preStep
      frobeniusCodomainIsotropic
  have frobeniusMem :=
    birationalNormalizedDivisor_mem_of_frobeniusType F factor.frobenius
      factor.frobenius_type sourceIsotropic
  have preStepIsometric : (preFrobenioid F).IsIsometric factor.preStep :=
    isGroupLikeType F factor.frobeniusCodomain
      ((preFrobenioid F).divisor factor.preStep)
  have preStepIsIso : IsIso factor.preStep :=
    frobeniusCodomainIsotropic factor.preStep factor.preStep_type
      preStepIsometric
  letI : IsIso factor.preStep := preStepIsIso
  have preStepMem := birationalNormalizedDivisor_mem_of_pullback F
    factor.preStep (birational_isPullback_of_isIso F factor.preStep)
      frobeniusCodomainIsotropic preStepCodomainIsotropic
  have pullbackMem := birationalNormalizedDivisor_mem_of_pullback F
    factor.pullback factor.pullback_type preStepCodomainIsotropic
      targetIsotropic
  rw [← factor.composite]
  simpa only [Category.assoc] using
    (birationalNormalizedDivisor_mem_comp F
      (factor.frobenius ≫ factor.preStep) factor.pullback
      (birationalNormalizedDivisor_mem_comp F factor.frobenius
        factor.preStep frobeniusMem preStepMem)
      pullbackMem)

/-- The normalized divisor of every birational arrow lies in `Phi^birat`.
For non-isotropic endpoints, zero-normalized gauge arrows reduce the claim to
the isotropic case. -/
theorem birationalNormalizedDivisor_mem
    {source target : BirationalCategory F} (arrow : source ⟶ target) :
    birationalNormalizedDivisor F arrow ∈
      birationalBaseDivisorRange F ((preFrobenioid F).base.obj source) := by
  let sourceGauge := birationalIsotropicGauge F source
  let targetGauge := birationalIsotropicGauge F target
  obtain ⟨extension, relation, _unique⟩ :=
    sourceGauge.lift (arrow ≫ targetGauge.hom) targetGauge.isotropic
  have extensionMem := birationalNormalizedDivisor_mem_of_isotropic F
    extension sourceGauge.isotropic targetGauge.isotropic
  have sourceGaugeZero : birationalNormalizedDivisor F sourceGauge.hom = 0 :=
    birationalNormalizedDivisor_isotropicGauge F source
  have targetGaugeZero : birationalNormalizedDivisor F targetGauge.hom = 0 :=
    birationalNormalizedDivisor_isotropicGauge F target
  have rightNormalized :
      birationalNormalizedDivisor F (arrow ≫ targetGauge.hom) =
        birationalNormalizedDivisor F arrow := by
    rw [birationalNormalizedDivisor_comp, targetGaugeZero,
      targetGauge.preStep.1]
    simp only [map_zero, zero_add]
    change (1 : ℕ) • birationalNormalizedDivisor F arrow = _
    exact one_nsmul _
  have normalizedRelation := congrArg (birationalNormalizedDivisor F)
    relation
  rw [← rightNormalized, ← normalizedRelation]
  exact birationalNormalizedDivisor_mem_comp F sourceGauge.hom extension
    (by rw [sourceGaugeZero]; exact AddSubgroup.zero_mem _)
    extensionMem

/-- The strict normalized factor through the restricted elementary category
`F_(Phi^birat)`. -/
def birationalRestrictedFactorFunctor :
    BirationalCategory F ⥤ BirationalRestrictedElementaryFrobenioid F where
  obj object := ⟨(preFrobenioid F).base.obj object⟩
  map arrow :=
    { base := (preFrobenioid F).base.map arrow
      divisor := ⟨birationalNormalizedDivisor F arrow,
        birationalNormalizedDivisor_mem F arrow⟩
      frobeniusDegree := (preFrobenioid F).frobeniusDegree arrow }
  map_id object := by
    apply RestrictedGroupifiedElementaryHom.ext
    · exact (preFrobenioid F).base.map_id object
    · apply Subtype.ext
      exact birationalNormalizedDivisor_id F object
    · exact (preFrobenioid F).frobeniusDegree_id object
  map_comp first second := by
    apply RestrictedGroupifiedElementaryHom.ext
    · exact (preFrobenioid F).base.map_comp first second
    · apply Subtype.ext
      exact birationalNormalizedDivisor_comp F first second
    · exact (preFrobenioid F).frobeniusDegree_comp first second

/-- The potential at an object is an invertible ambient elementary arrow.
It is the component of the 1-isomorphism from the normalized factor to the
raw groupified functor. -/
def birationalNormalizationIsoComponent (object : BirationalCategory F) :
    ((birationalRestrictedFactorFunctor F ⋙
        birationalRestrictedElementaryInclusion F).obj object) ≅
      (groupifiedBirationalFunctor F).obj object where
  hom :=
    { base := 𝟙 _
      divisor := birationalObjectPotential F object
      frobeniusDegree := 1 }
  inv :=
    { base := 𝟙 _
      divisor := -birationalObjectPotential F object
      frobeniusDegree := 1 }
  hom_inv_id := by
    apply GroupifiedElementaryHom.ext
    · change (𝟙 _ ≫ 𝟙 _) = 𝟙 _
      simp
    · change F.preFrobenioid.divisorMonoid.gpPullback (𝟙 _)
          (-birationalObjectPotential F object) +
        (1 : ℕ) • birationalObjectPotential F object = 0
      rw [F.preFrobenioid.divisorMonoid.gpPullback_id]
      change AddMonoidHom.id _ (-_) + (1 : ℕ) • _ = 0
      rw [AddMonoidHom.id_apply, one_nsmul, neg_add_cancel]
    · rfl
  inv_hom_id := by
    apply GroupifiedElementaryHom.ext
    · change (𝟙 _ ≫ 𝟙 _) = 𝟙 _
      simp
    · change F.preFrobenioid.divisorMonoid.gpPullback (𝟙 _)
          (birationalObjectPotential F object) +
        (1 : ℕ) • (-birationalObjectPotential F object) = 0
      rw [F.preFrobenioid.divisorMonoid.gpPullback_id]
      change AddMonoidHom.id _ _ + (1 : ℕ) • (-_) = 0
      rw [AddMonoidHom.id_apply, one_nsmul, add_neg_cancel]
    · rfl

/-- Proposition 4.4(iii)'s literal 1-commutative factorization: after the
objectwise potential normalization, inclusion into `F_(Phi^gp)` is naturally
isomorphic to the original groupified functor. -/
def birationalRestrictedFactorIso :
    birationalRestrictedFactorFunctor F ⋙
        birationalRestrictedElementaryInclusion F ≅
      groupifiedBirationalFunctor F :=
  NatIso.ofComponents (birationalNormalizationIsoComponent F) (by
    intro source target arrow
    dsimp only [Functor.comp_obj, Functor.comp_map,
      birationalRestrictedFactorFunctor,
      birationalRestrictedElementaryInclusion,
      RestrictedGroupifiedElementaryFrobenioid.inclusion,
      birationalNormalizationIsoComponent]
    apply GroupifiedElementaryHom.ext
    · change (preFrobenioid F).base.map arrow ≫ 𝟙 _ =
        𝟙 _ ≫ ((groupifiedBirationalFunctor F).map arrow).base
      rw [groupifiedBirationalFunctor_map_base]
      simp
    · dsimp only [CategoryStruct.comp,
        GroupifiedElementaryFrobenioid.instCategory,
        GroupifiedElementaryHom.comp]
      rw [groupifiedBirationalFunctor_map_frobeniusDegree]
      change F.preFrobenioid.divisorMonoid.gpPullback
          ((preFrobenioid F).base.map arrow)
          (birationalObjectPotential F target) +
        (1 : ℕ+).1 • birationalNormalizedDivisor F arrow =
      F.preFrobenioid.divisorMonoid.gpPullback (𝟙 _)
          (birationalRawDivisor F arrow) +
        ((preFrobenioid F).frobeniusDegree arrow).1 •
          birationalObjectPotential F source
      rw [F.preFrobenioid.divisorMonoid.gpPullback_id]
      change _ + (1 : ℕ) • birationalNormalizedDivisor F arrow =
        AddMonoidHom.id _ (birationalRawDivisor F arrow) + _
      rw [one_nsmul, AddMonoidHom.id_apply, birationalNormalizedDivisor]
      abel
    · dsimp only [CategoryStruct.comp,
        GroupifiedElementaryFrobenioid.instCategory,
        GroupifiedElementaryHom.comp]
      change (preFrobenioid F).frobeniusDegree arrow * 1 =
        1 * ((groupifiedBirationalFunctor F).map arrow).frobeniusDegree
      rw [groupifiedBirationalFunctor_map_frobeniusDegree]
      simp)

end

end Iut.FrobenioidBirationalization
