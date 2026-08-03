/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Frobenioid
import Mathlib.CategoryTheory.Skeletal

/-!
# Frobenioid model-type foundations

This file formalizes the source definitions needed for the model-type assertion
of Frobenioids I, Theorem 5.2(ii): Frobenius normalization from Definition
1.2(iv), and base-sections, Frobenius-sections, base-Frobenius pairs, and
pre-model type from Definition 2.7.
-/

open CategoryTheory

namespace Iut.PreFrobenioid

universe u

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable (P : PreFrobenioid C D IsFSM)

/-- Frobenioids I, Definition 1.2(iv): a Frobenius-normalized object. -/
def IsFrobeniusNormalized (X : C) : Prop :=
  ∀ (phi : X ⟶ X), P.IsBaseIdentity phi →
    ∀ alpha : P.LinearBaseIdentityEndomorphism X,
      phi ≫ (alpha ^ (P.frobeniusDegree phi).val).hom =
        alpha.hom ≫ phi

/-- Every object of the pre-Frobenioid is Frobenius-normalized. -/
def IsFrobeniusNormalizedType : Prop :=
  ∀ X : C, P.IsFrobeniusNormalized X

/-- Frobenioids I, Definition 1.2(iv): the divisor monoid at an object is zero. -/
def IsGroupLike (X : C) : Prop :=
  ∀ value : (P.divisorMonoid.obj ((P.base).obj X)).carrier, value = 0

/-- Every object of the pre-Frobenioid is group-like. -/
def IsGroupLikeType : Prop :=
  ∀ X : C, P.IsGroupLike X

/--
Frobenioids I, Definition 2.7's standing hypothesis: every object of the
Frobenioid is isotropic.
-/
def IsIsotropicType : Prop :=
  ∀ X : C, P.IsIsotropic X

/--
Frobenioids I, Definition 2.7(i).  The section category is skeletal, embeds
faithfully through actual pullback arrows, projects equivalently to the base,
and consists of Frobenius-trivial objects.
-/
structure BaseSection where
  sectionCategory : Cat.{u, u}
  inclusion : sectionCategory ⥤ C
  skeletal : Skeletal sectionCategory
  inclusion_faithful : inclusion.Faithful
  map_isPullback :
    ∀ {X Y : sectionCategory} (f : X ⟶ Y), P.IsPullback (inclusion.map f)
  base_isEquivalence : (inclusion ⋙ P.base).IsEquivalence
  object_frobeniusTrivial :
    ∀ X : sectionCategory, P.IsFrobeniusTrivial (inclusion.obj X)

/--
Frobenioids I, Definition 2.7(ii): a multiplicative Frobenius section as
natural endomorphisms of the base-section inclusion.
-/
structure FrobeniusSection (baseSection : P.BaseSection) where
  lift : ℕ+ → (baseSection.inclusion ⟶ baseSection.inclusion)
  map_one : lift 1 = 𝟙 baseSection.inclusion
  map_mul : ∀ m n, lift (m * n) = lift m ≫ lift n
  degree_section :
    ∀ n X, P.frobeniusDegree ((lift n).app X) = n
  base_identity :
    ∀ n X, P.IsBaseIdentity ((lift n).app X)
  of_frobenius_type :
    ∀ n X, P.IsOfFrobeniusType ((lift n).app X)

/-- Frobenioids I, Definition 2.7(iii): a base-Frobenius pair. -/
structure BaseFrobeniusPair where
  baseSection : P.BaseSection
  frobeniusSection : P.FrobeniusSection baseSection

/--
Frobenioids I, Definition 2.7(iii): isotropic type together with existence of
a base-Frobenius pair.
-/
def IsPreModelType : Prop :=
  P.IsIsotropicType ∧ Nonempty P.BaseFrobeniusPair

/-- Every object of a pre-model-type Frobenioid is isotropic. -/
theorem IsPreModelType.isIsotropic
    (hypothesis : P.IsPreModelType) (X : C) :
    P.IsIsotropic X :=
  hypothesis.1 X

/-- A pre-model-type Frobenioid admits a base-Frobenius pair. -/
theorem IsPreModelType.baseFrobeniusPair_nonempty
    (hypothesis : P.IsPreModelType) :
    Nonempty P.BaseFrobeniusPair :=
  hypothesis.2

/--
Negative regression: even when a base-Frobenius pair exists, one
non-isotropic object prevents the Frobenioid from being of pre-model type.
-/
theorem baseFrobeniusPair_not_sufficient
  (pair : Nonempty P.BaseFrobeniusPair)
    {X : C} (not_isotropic : ¬ P.IsIsotropic X) :
    Nonempty P.BaseFrobeniusPair ∧ ¬ P.IsPreModelType :=
  ⟨pair, fun hypothesis ↦
    not_isotropic (IsPreModelType.isIsotropic P hypothesis X)⟩

/--
Frobenioids I, Definition 4.5(i): an object whose image in a chosen
birationalization is Frobenius-normalized.
-/
def IsBirationallyFrobeniusNormalized
    (_P : PreFrobenioid C D IsFSM)
    {Cbirat : Type u} [Category.{u} Cbirat]
    (Pbirat : PreFrobenioid Cbirat D IsFSM) (inclusion : C ⥤ Cbirat)
    (X : C) : Prop :=
  Pbirat.IsFrobeniusNormalized (inclusion.obj X)

/-- Every object is birationally Frobenius-normalized. -/
def IsBirationallyFrobeniusNormalizedType
    (P : PreFrobenioid C D IsFSM)
    {Cbirat : Type u} [Category.{u} Cbirat]
    (Pbirat : PreFrobenioid Cbirat D IsFSM) (inclusion : C ⥤ Cbirat) : Prop :=
  ∀ X : C, P.IsBirationallyFrobeniusNormalized Pbirat inclusion X

/-- Definition 4.5(i): pre-model plus birational Frobenius normalization. -/
def IsModelType
    {Cbirat : Type u} [Category.{u} Cbirat]
    (Pbirat : PreFrobenioid Cbirat D IsFSM) (inclusion : C ⥤ Cbirat) : Prop :=
  P.IsPreModelType ∧
    P.IsBirationallyFrobeniusNormalizedType Pbirat inclusion

end Iut.PreFrobenioid
