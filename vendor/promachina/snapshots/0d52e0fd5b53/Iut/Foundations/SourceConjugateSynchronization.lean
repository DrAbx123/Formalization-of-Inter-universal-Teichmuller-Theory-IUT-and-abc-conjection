/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceThetaEvaluation

/-!
# Single-inner-automorphism conjugate synchronization

IUT II, Corollary 3.5 requires collections of restriction isomorphisms to be
well-defined up to one inner automorphism, independent of the label.  This file
models that requirement as a quotient of multiplicative isomorphisms by one
global group element acting on the entire target.
-/

namespace Iut

universe u

/--
Two multiplicative isomorphisms differ by a single inner action when one
global group element postcomposes every value of the first isomorphism.
-/
def MulEquivsDifferBySingleInner
    {Inner Source Target : Type u}
    [Group Inner] [Monoid Source] [Monoid Target]
    (innerAction : Inner →* MulAut Target)
    (first second : Source ≃* Target) : Prop :=
  ∃ conjugator : Inner,
    ∀ value,
      second value =
        innerAction conjugator (first value)

namespace MulEquivsDifferBySingleInner

variable
  {Inner Source Target : Type u}
  [Group Inner] [Monoid Source] [Monoid Target]
  {innerAction : Inner →* MulAut Target}
  {first second third : Source ≃* Target}

theorem refl (first : Source ≃* Target) :
    MulEquivsDifferBySingleInner
      innerAction first first := by
  refine ⟨1, ?_⟩
  intro value
  rw [map_one]
  rfl

theorem symm
    (h :
      MulEquivsDifferBySingleInner
        innerAction first second) :
    MulEquivsDifferBySingleInner
      innerAction second first := by
  rcases h with ⟨conjugator, h⟩
  refine ⟨conjugator⁻¹, ?_⟩
  intro value
  rw [h value]
  symm
  calc
    innerAction conjugator⁻¹
        (innerAction conjugator (first value)) =
      (innerAction conjugator⁻¹ *
        innerAction conjugator) (first value) :=
      rfl
    _ =
      innerAction
          (conjugator⁻¹ * conjugator)
          (first value) := by
        rw [map_mul]
    _ = first value := by simp

theorem trans
    (hFirstSecond :
      MulEquivsDifferBySingleInner
        innerAction first second)
    (hSecondThird :
      MulEquivsDifferBySingleInner
        innerAction second third) :
    MulEquivsDifferBySingleInner
      innerAction first third := by
  rcases hFirstSecond with
    ⟨firstConjugator, hFirst⟩
  rcases hSecondThird with
    ⟨secondConjugator, hSecond⟩
  refine
    ⟨secondConjugator * firstConjugator, ?_⟩
  intro value
  rw [hSecond value, hFirst value]
  calc
    innerAction secondConjugator
        (innerAction firstConjugator
          (first value)) =
      (innerAction secondConjugator *
        innerAction firstConjugator)
          (first value) :=
      rfl
    _ =
      innerAction
          (secondConjugator * firstConjugator)
          (first value) := by
        rw [map_mul]

end MulEquivsDifferBySingleInner

/-- The setoid of restriction isomorphisms modulo one global inner action. -/
def singleInnerIsomorphismSetoid
    {Inner Source Target : Type u}
    [Group Inner] [Monoid Source] [Monoid Target]
    (innerAction : Inner →* MulAut Target) :
    Setoid (Source ≃* Target) where
  r :=
    MulEquivsDifferBySingleInner innerAction
  iseqv :=
    { refl := fun isomorphism =>
        MulEquivsDifferBySingleInner.refl
          isomorphism
      symm := fun h =>
        MulEquivsDifferBySingleInner.symm h
      trans := fun firstSecond secondThird =>
        MulEquivsDifferBySingleInner.trans
          firstSecond secondThird }

/--
An isomorphism well-defined up to one inner automorphism of the entire target.
-/
def SourceSingleInnerIsomorphismClass
    {Inner Source Target : Type u}
    [Group Inner] [Monoid Source] [Monoid Target]
    (innerAction : Inner →* MulAut Target) : Type u :=
  Quotient
    (singleInnerIsomorphismSetoid
      (Source := Source) innerAction)

namespace SourceSingleInnerIsomorphismClass

variable
  {Inner Source Target : Type u}
  [Group Inner] [Monoid Source] [Monoid Target]
  {innerAction : Inner →* MulAut Target}

/-- The synchronized class represented by one multiplicative isomorphism. -/
def classOf
    (isomorphism : Source ≃* Target) :
    SourceSingleInnerIsomorphismClass
      (Source := Source) innerAction :=
  Quotient.mk
    (singleInnerIsomorphismSetoid
      (Source := Source) innerAction)
    isomorphism

theorem classOf_eq
    {first second : Source ≃* Target}
    (h :
      MulEquivsDifferBySingleInner
        innerAction first second) :
    classOf (innerAction := innerAction) first =
      classOf (innerAction := innerAction) second :=
  Quotient.sound h

end SourceSingleInnerIsomorphismClass

/--
The Corollary 3.5 restriction-isomorphism class into the full symmetrized
product, modulo one transported base-group action on all labels.
-/
abbrev SourceIUTIISynchronizedRestrictionIsomorphismClass
    {l : PrimeGeFive}
    (symmetry :
      SourceIUTIISymmetrizingIsomorphisms.{u} l)
    (Source : Type u) [Monoid Source] :=
  SourceSingleInnerIsomorphismClass
    symmetry.diagonalActionHom
    (Source := Source)
    (Target :=
      ∀ label,
        (symmetry.pair label).monoidCarrier)

/--
The fixed groups, monoids, actions, and first group inclusion in the compatible
diagram of IUT II, Corollary 3.5(i).

The three groups model `Π_X`, `Π_v`, and the diagonal labeled copy of `G_v`.
The two monoids model the constant monoid before and after restriction.
-/
structure SourceIUTIICorollary35RestrictionContext where
  baseGroup : TopologicalGroupCat.{u}
  ambientGroup : TopologicalGroupCat.{u}
  labeledGroup : TopologicalGroupCat.{u}
  sourceMonoid : Type u
  targetMonoid : Type u
  [sourceMonoidStructure : Monoid sourceMonoid]
  [targetMonoidStructure : Monoid targetMonoid]
  [sourceTopology : TopologicalSpace sourceMonoid]
  [targetTopology : TopologicalSpace targetMonoid]
  [sourceContinuousMul : ContinuousMul sourceMonoid]
  [targetContinuousMul : ContinuousMul targetMonoid]
  ambientToBase : ambientGroup →ₜ* baseGroup
  sourceAction : baseGroup →* MulAut sourceMonoid
  targetAction : labeledGroup →* MulAut targetMonoid
  continuous_source_action :
    Continuous fun input : baseGroup × sourceMonoid =>
      sourceAction input.1 input.2
  continuous_target_action :
    Continuous fun input : labeledGroup × targetMonoid =>
      targetAction input.1 input.2

namespace SourceIUTIICorollary35RestrictionContext

attribute [instance] sourceMonoidStructure targetMonoidStructure
  sourceTopology targetTopology sourceContinuousMul targetContinuousMul

end SourceIUTIICorollary35RestrictionContext

/--
The compatible group/monoid morphisms in the third display of IUT II,
Corollary 3.5(i).

The equivariance equation follows the entire composite from the diagonal
labeled group through the ambient group and into the single base group.
-/
structure SourceIUTIICorollary35RestrictionDiagram
    (context : SourceIUTIICorollary35RestrictionContext.{u}) where
  labeledToAmbient :
    context.labeledGroup →ₜ* context.ambientGroup
  monoidIso :
    context.sourceMonoid ≃ₜ* context.targetMonoid
  equivariant :
    ∀ groupElement monoidElement,
      monoidIso
          (context.sourceAction
            (context.ambientToBase
              (labeledToAmbient groupElement))
            monoidElement) =
        context.targetAction groupElement
          (monoidIso monoidElement)

/--
The single-basepoint conjugation action used to compare two Corollary 3.5
restriction diagrams.

One element of `baseGroup` acts simultaneously on the ambient group and the
target monoid.  The first compatibility equation says that its action on the
ambient group is genuine conjugation after inclusion into the base group.
-/
structure SourceIUTIICorollary35SingleBasepointAction
    (context : SourceIUTIICorollary35RestrictionContext.{u}) where
  ambientAction :
    context.baseGroup →*
      MulAut context.ambientGroup
  targetAction :
    context.baseGroup →*
      MulAut context.targetMonoid
  continuous_ambient_action :
    Continuous fun input :
      context.baseGroup × context.ambientGroup =>
        ambientAction input.1 input.2
  continuous_target_action :
    Continuous fun input :
      context.baseGroup × context.targetMonoid =>
        targetAction input.1 input.2
  ambientToBase_equivariant :
    ∀ baseElement ambientElement,
      context.ambientToBase
          (ambientAction baseElement ambientElement) =
        MulAut.conj baseElement
          (context.ambientToBase ambientElement)

/--
Two compatible restriction diagrams differ by a single inner automorphism
when one base-group element simultaneously conjugates the group map and the
monoid isomorphism.  In particular, the witness cannot depend on a label,
group element, or monoid element.
-/
def RestrictionDiagramsDifferBySingleInner
    {context :
      SourceIUTIICorollary35RestrictionContext.{u}}
    (singleBasepoint :
      SourceIUTIICorollary35SingleBasepointAction context)
    (first second :
      SourceIUTIICorollary35RestrictionDiagram context) : Prop :=
  ∃ conjugator : context.baseGroup,
    (∀ groupElement,
      second.labeledToAmbient groupElement =
        singleBasepoint.ambientAction conjugator
          (first.labeledToAmbient groupElement)) ∧
    (∀ monoidElement,
      second.monoidIso monoidElement =
        singleBasepoint.targetAction conjugator
          (first.monoidIso monoidElement))

namespace RestrictionDiagramsDifferBySingleInner

variable
  {context :
    SourceIUTIICorollary35RestrictionContext.{u}}
  {singleBasepoint :
    SourceIUTIICorollary35SingleBasepointAction context}
  {first second third :
    SourceIUTIICorollary35RestrictionDiagram context}

/--
After inclusion in the single base group, the group-map component differs by
literal group conjugation by the same element that controls the monoid map.
-/
theorem afterBaseInclusion
    (h :
      RestrictionDiagramsDifferBySingleInner
        singleBasepoint first second) :
    ∃ conjugator : context.baseGroup,
      (∀ groupElement,
        context.ambientToBase
            (second.labeledToAmbient groupElement) =
          MulAut.conj conjugator
            (context.ambientToBase
              (first.labeledToAmbient groupElement))) ∧
      (∀ monoidElement,
        second.monoidIso monoidElement =
          singleBasepoint.targetAction conjugator
            (first.monoidIso monoidElement)) := by
  rcases h with
    ⟨conjugator, hgroup, hmonoid⟩
  refine ⟨conjugator, ?_, hmonoid⟩
  intro groupElement
  rw [hgroup groupElement]
  exact
    singleBasepoint.ambientToBase_equivariant
      conjugator
      (first.labeledToAmbient groupElement)

theorem refl
    (diagram :
      SourceIUTIICorollary35RestrictionDiagram context) :
    RestrictionDiagramsDifferBySingleInner
      singleBasepoint diagram diagram := by
  refine ⟨1, ?_, ?_⟩
  · intro groupElement
    rw [map_one]
    rfl
  · intro monoidElement
    rw [map_one]
    rfl

theorem symm
    (h :
      RestrictionDiagramsDifferBySingleInner
        singleBasepoint first second) :
    RestrictionDiagramsDifferBySingleInner
      singleBasepoint second first := by
  rcases h with
    ⟨conjugator, hgroup, hmonoid⟩
  refine ⟨conjugator⁻¹, ?_, ?_⟩
  · intro groupElement
    rw [hgroup groupElement]
    symm
    calc
      singleBasepoint.ambientAction conjugator⁻¹
          (singleBasepoint.ambientAction conjugator
            (first.labeledToAmbient groupElement)) =
        (singleBasepoint.ambientAction conjugator⁻¹ *
          singleBasepoint.ambientAction conjugator)
            (first.labeledToAmbient groupElement) :=
        rfl
      _ =
        singleBasepoint.ambientAction
            (conjugator⁻¹ * conjugator)
            (first.labeledToAmbient groupElement) := by
          rw [map_mul]
      _ = first.labeledToAmbient groupElement := by
        simp
  · intro monoidElement
    rw [hmonoid monoidElement]
    symm
    calc
      singleBasepoint.targetAction conjugator⁻¹
          (singleBasepoint.targetAction conjugator
            (first.monoidIso monoidElement)) =
        (singleBasepoint.targetAction conjugator⁻¹ *
          singleBasepoint.targetAction conjugator)
            (first.monoidIso monoidElement) :=
        rfl
      _ =
        singleBasepoint.targetAction
            (conjugator⁻¹ * conjugator)
            (first.monoidIso monoidElement) := by
          rw [map_mul]
      _ = first.monoidIso monoidElement := by
        simp

theorem trans
    (hFirstSecond :
      RestrictionDiagramsDifferBySingleInner
        singleBasepoint first second)
    (hSecondThird :
      RestrictionDiagramsDifferBySingleInner
        singleBasepoint second third) :
    RestrictionDiagramsDifferBySingleInner
      singleBasepoint first third := by
  rcases hFirstSecond with
    ⟨firstConjugator, hFirstGroup, hFirstMonoid⟩
  rcases hSecondThird with
    ⟨secondConjugator, hSecondGroup, hSecondMonoid⟩
  refine
    ⟨secondConjugator * firstConjugator, ?_, ?_⟩
  · intro groupElement
    rw [hSecondGroup groupElement,
      hFirstGroup groupElement]
    calc
      singleBasepoint.ambientAction secondConjugator
          (singleBasepoint.ambientAction firstConjugator
            (first.labeledToAmbient groupElement)) =
        (singleBasepoint.ambientAction secondConjugator *
          singleBasepoint.ambientAction firstConjugator)
            (first.labeledToAmbient groupElement) :=
        rfl
      _ =
        singleBasepoint.ambientAction
            (secondConjugator * firstConjugator)
            (first.labeledToAmbient groupElement) := by
          rw [map_mul]
  · intro monoidElement
    rw [hSecondMonoid monoidElement,
      hFirstMonoid monoidElement]
    calc
      singleBasepoint.targetAction secondConjugator
          (singleBasepoint.targetAction firstConjugator
            (first.monoidIso monoidElement)) =
        (singleBasepoint.targetAction secondConjugator *
          singleBasepoint.targetAction firstConjugator)
            (first.monoidIso monoidElement) :=
        rfl
      _ =
        singleBasepoint.targetAction
            (secondConjugator * firstConjugator)
            (first.monoidIso monoidElement) := by
          rw [map_mul]

end RestrictionDiagramsDifferBySingleInner

/-- The setoid of full compatible restriction diagrams modulo one conjugator. -/
def singleInnerRestrictionDiagramSetoid
    {context :
      SourceIUTIICorollary35RestrictionContext.{u}}
    (singleBasepoint :
      SourceIUTIICorollary35SingleBasepointAction context) :
    Setoid
      (SourceIUTIICorollary35RestrictionDiagram context) where
  r :=
    RestrictionDiagramsDifferBySingleInner singleBasepoint
  iseqv :=
    { refl := RestrictionDiagramsDifferBySingleInner.refl
      symm := RestrictionDiagramsDifferBySingleInner.symm
      trans := RestrictionDiagramsDifferBySingleInner.trans }

/--
The full Corollary 3.5(i) compatible-morphism diagram, well-defined up to one
inner automorphism of the single basepoint group.
-/
def SourceIUTIISynchronizedRestrictionDiagramClass
    {context :
      SourceIUTIICorollary35RestrictionContext.{u}}
    (singleBasepoint :
      SourceIUTIICorollary35SingleBasepointAction context) :
    Type u :=
  Quotient
    (singleInnerRestrictionDiagramSetoid singleBasepoint)

namespace SourceIUTIISynchronizedRestrictionDiagramClass

variable
  {context :
    SourceIUTIICorollary35RestrictionContext.{u}}
  {singleBasepoint :
    SourceIUTIICorollary35SingleBasepointAction context}

/-- The synchronized class represented by one compatible restriction diagram. -/
def classOf
    (diagram :
      SourceIUTIICorollary35RestrictionDiagram context) :
    SourceIUTIISynchronizedRestrictionDiagramClass
      singleBasepoint :=
  Quotient.mk
    (singleInnerRestrictionDiagramSetoid singleBasepoint)
    diagram

theorem classOf_eq
    {first second :
      SourceIUTIICorollary35RestrictionDiagram context}
    (h :
      RestrictionDiagramsDifferBySingleInner
        singleBasepoint first second) :
    classOf (singleBasepoint := singleBasepoint) first =
      classOf (singleBasepoint := singleBasepoint) second :=
  Quotient.sound h

end SourceIUTIISynchronizedRestrictionDiagramClass

namespace SourceIUTIICorollary35RestrictionDiagram

variable
  {context :
    SourceIUTIICorollary35RestrictionContext.{u}}
  {singleBasepoint :
    SourceIUTIICorollary35SingleBasepointAction context}

/--
Forget the group-map component of a compatible diagram while retaining its
single-inner-automorphism class of monoid isomorphisms.
-/
def monoidIsomorphismClass
    (diagram :
      SourceIUTIICorollary35RestrictionDiagram context) :
    SourceSingleInnerIsomorphismClass
      (Source := context.sourceMonoid)
      (Target := context.targetMonoid)
      singleBasepoint.targetAction :=
  SourceSingleInnerIsomorphismClass.classOf
    (Source := context.sourceMonoid)
    (Target := context.targetMonoid)
    (innerAction := singleBasepoint.targetAction)
    diagram.monoidIso.toMulEquiv

theorem monoidIsomorphismClass_eq
    {first second :
      SourceIUTIICorollary35RestrictionDiagram context}
    (h :
      RestrictionDiagramsDifferBySingleInner
        singleBasepoint first second) :
    monoidIsomorphismClass
        (singleBasepoint := singleBasepoint) first =
      monoidIsomorphismClass
        (singleBasepoint := singleBasepoint) second := by
  apply SourceSingleInnerIsomorphismClass.classOf_eq
  rcases h with
    ⟨conjugator, _hgroup, hmonoid⟩
  exact ⟨conjugator, hmonoid⟩

/--
The full synchronized diagram class descends to its monoid-isomorphism class.
Thus the full diagram quotient refines the monoid-only quotient.
-/
def synchronizedClassToMonoidIsomorphismClass :
    SourceIUTIISynchronizedRestrictionDiagramClass
        singleBasepoint →
      SourceSingleInnerIsomorphismClass
        (Source := context.sourceMonoid)
        (Target := context.targetMonoid)
        singleBasepoint.targetAction :=
  Quotient.lift
    (monoidIsomorphismClass
      (singleBasepoint := singleBasepoint))
    (by
      intro first second h
      exact monoidIsomorphismClass_eq h)

@[simp]
theorem synchronizedClassToMonoidIsomorphismClass_mk
    (diagram :
      SourceIUTIICorollary35RestrictionDiagram context) :
    synchronizedClassToMonoidIsomorphismClass
        (singleBasepoint := singleBasepoint)
        (SourceIUTIISynchronizedRestrictionDiagramClass.classOf
          (singleBasepoint := singleBasepoint) diagram) =
      monoidIsomorphismClass
        (singleBasepoint := singleBasepoint) diagram :=
  rfl

end SourceIUTIICorollary35RestrictionDiagram

end Iut
