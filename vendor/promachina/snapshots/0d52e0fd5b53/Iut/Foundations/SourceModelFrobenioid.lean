/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Frobenioid
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# The model-Frobenioid category of Frobenioids I, Theorem 5.2

For a divisorial monoid `Phi`, a group-like rational-function monoid `B`, and
the natural divisor map `DivB : B -> Phi^gp`, Theorem 5.2(i) constructs a
category explicitly. Objects are pairs `(A_D, alpha)`. An arrow consists of a
positive Frobenius degree, a base arrow, an effective divisor, and a rational
function satisfying the source balance equation.

This file implements that category, its exact composition law, and its
structure functor to the elementary Frobenioid. It also derives the connected
and totally epimorphic presentation required by Definition 1.1(iv). The
remaining proof of Theorem 5.2(ii), that this category satisfies every
Frobenioid axiom and has the stated model properties, is not asserted here.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceModelFrobenioid

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}

/-- A group-like monoid on the base category, written additively as in FrdI 5.2. -/
structure GroupLikeAddMonoidOn
    (D : Type u) [Category.{u} D]
    (IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop) where
  obj : D → Type u
  addCommGroup : ∀ X, AddCommGroup (obj X)
  pullback : ∀ {X Y : D}, (X ⟶ Y) → (obj Y →+ obj X)
  pullback_id : ∀ X, pullback (𝟙 X) = AddMonoidHom.id (obj X)
  pullback_comp :
    ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g)
  pullback_injective :
    ∀ {X Y : D} (f : X ⟶ Y), Function.Injective (pullback f)
  fsmPullbackIsIso :
    ∀ {X Y : D} (f : X ⟶ Y), IsFSM f → Function.Bijective (pullback f)

attribute [instance] GroupLikeAddMonoidOn.addCommGroup

/-- Pullback on the groupification of a divisorial monoid. -/
noncomputable abbrev gpPullback
    (Phi : DivisorialMonoidOn D IsFSM) {X Y : D} (f : X ⟶ Y) :
    Algebra.GrothendieckAddGroup (Phi.obj Y).carrier →+
      Algebra.GrothendieckAddGroup (Phi.obj X).carrier :=
  Phi.gpPullback f

@[simp]
theorem gpPullback_of
    (Phi : DivisorialMonoidOn D IsFSM) {X Y : D} (f : X ⟶ Y)
    (value : (Phi.obj Y).carrier) :
    gpPullback Phi f (Algebra.GrothendieckAddGroup.of value) =
      Algebra.GrothendieckAddGroup.of (Phi.pullback f value) :=
  Phi.gpPullback_of f value

theorem gpPullback_id
    (Phi : DivisorialMonoidOn D IsFSM) (X : D) :
    gpPullback Phi (𝟙 X) =
      AddMonoidHom.id (Algebra.GrothendieckAddGroup (Phi.obj X).carrier) :=
  Phi.gpPullback_id X

theorem gpPullback_comp
    (Phi : DivisorialMonoidOn D IsFSM)
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    gpPullback Phi (f ≫ g) =
      (gpPullback Phi f).comp (gpPullback Phi g) :=
  Phi.gpPullback_comp f g

/-- Input data of the explicit model-Frobenioid construction in FrdI 5.2. -/
structure Input
    (Phi : DivisorialMonoidOn D IsFSM) where
  rationalFunctions : GroupLikeAddMonoidOn D IsFSM
  divisor :
    ∀ X : D,
      rationalFunctions.obj X →+
        Algebra.GrothendieckAddGroup (Phi.obj X).carrier
  divisor_natural :
    ∀ {X Y : D} (f : X ⟶ Y) (value : rationalFunctions.obj Y),
      divisor X (rationalFunctions.pullback f value) =
        gpPullback Phi f (divisor Y value)

namespace Input

variable {Phi : DivisorialMonoidOn D IsFSM}

/-- The paper's `Phi_birat`, the image of the rational-function divisor map. -/
def birationalDivisors
    (data : Input Phi) (X : D) :
    AddSubgroup (Algebra.GrothendieckAddGroup (Phi.obj X).carrier) :=
  (data.divisor X).range

/-- Pullback carries the birational divisor subgroup into the one at the source. -/
theorem gpPullback_mem_birationalDivisors
    (data : Input Phi) {X Y : D} (f : X ⟶ Y)
    {value : Algebra.GrothendieckAddGroup (Phi.obj Y).carrier}
    (hvalue : value ∈ data.birationalDivisors Y) :
    gpPullback Phi f value ∈ data.birationalDivisors X := by
  rcases hvalue with ⟨rationalFunction, rfl⟩
  exact ⟨data.rationalFunctions.pullback f rationalFunction,
    data.divisor_natural f rationalFunction⟩

end Input

/-- An object `(A_D, alpha)` of the model Frobenioid. -/
structure Object (Phi : DivisorialMonoidOn D IsFSM) where
  base : D
  divisorClass : Algebra.GrothendieckAddGroup (Phi.obj base).carrier

/-- The four source fields of a model-Frobenioid arrow and their balance equation. -/
@[ext]
structure Hom
    (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi)
    (source target : Object Phi) where
  frobeniusDegree : ℕ+
  base : source.base ⟶ target.base
  divisor : (Phi.obj source.base).carrier
  rationalFunction : data.rationalFunctions.obj source.base
  balance :
    frobeniusDegree.val • source.divisorClass +
        Algebra.GrothendieckAddGroup.of divisor =
      gpPullback Phi base target.divisorClass +
        data.divisor source.base rationalFunction

namespace Hom

variable (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi)

/-- Identity arrow from Theorem 5.2(i). -/
def id (source : Object Phi) : Hom Phi data source source where
  frobeniusDegree := 1
  base := 𝟙 source.base
  divisor := 0
  rationalFunction := 0
  balance := by
    simp only [map_zero, add_zero]
    norm_num
    rw [gpPullback_id]
    exact one_nsmul _

/-- Composition with the exact divisor and rational-function formulas of 5.2(i). -/
def comp {source middle target : Object Phi}
    (first : Hom Phi data source middle)
    (second : Hom Phi data middle target) :
    Hom Phi data source target where
  frobeniusDegree := first.frobeniusDegree * second.frobeniusDegree
  base := first.base ≫ second.base
  divisor :=
    Phi.pullback first.base second.divisor +
      second.frobeniusDegree.val • first.divisor
  rationalFunction :=
    data.rationalFunctions.pullback first.base second.rationalFunction +
      second.frobeniusDegree.val • first.rationalFunction
  balance := by
    change
      (first.frobeniusDegree.val * second.frobeniusDegree.val) •
            source.divisorClass +
          Algebra.GrothendieckAddGroup.of
            (Phi.pullback first.base second.divisor +
              second.frobeniusDegree.val • first.divisor) = _
    calc
      _ = gpPullback Phi first.base
              (Algebra.GrothendieckAddGroup.of second.divisor) +
            second.frobeniusDegree.val •
              (first.frobeniusDegree.val • source.divisorClass +
                Algebra.GrothendieckAddGroup.of first.divisor) := by
          simp only [map_add, map_nsmul, gpPullback_of]
          rw [mul_nsmul, nsmul_add]
          abel
      _ = gpPullback Phi first.base
              (Algebra.GrothendieckAddGroup.of second.divisor) +
            second.frobeniusDegree.val •
              (gpPullback Phi first.base middle.divisorClass +
                data.divisor source.base first.rationalFunction) := by
          rw [first.balance]
      _ = gpPullback Phi first.base
              (second.frobeniusDegree.val • middle.divisorClass +
                Algebra.GrothendieckAddGroup.of second.divisor) +
            second.frobeniusDegree.val •
              data.divisor source.base first.rationalFunction := by
          simp only [map_add, map_nsmul, nsmul_add]
          abel
      _ = gpPullback Phi first.base
              (gpPullback Phi second.base target.divisorClass +
                data.divisor middle.base second.rationalFunction) +
            second.frobeniusDegree.val •
              data.divisor source.base first.rationalFunction := by
          rw [second.balance]
      _ = gpPullback Phi (first.base ≫ second.base) target.divisorClass +
            data.divisor source.base
              (data.rationalFunctions.pullback first.base
                second.rationalFunction) +
            second.frobeniusDegree.val •
              data.divisor source.base first.rationalFunction := by
          rw [map_add, gpPullback_comp, ← data.divisor_natural]
          rfl
      _ = gpPullback Phi (first.base ≫ second.base) target.divisorClass +
            data.divisor source.base
              (data.rationalFunctions.pullback first.base
                  second.rationalFunction +
                second.frobeniusDegree.val • first.rationalFunction) := by
          rw [map_add, map_nsmul, add_assoc]

end Hom

/-- The source category constructed in Frobenioids I, Theorem 5.2(i). -/
def Carrier
    (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi) :=
  let _sourceData := data
  Object Phi

instance carrierCategory
    (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi) :
    Category.{u} (Carrier Phi data) where
  Hom := Hom Phi data
  id := Hom.id Phi data
  comp := Hom.comp Phi data
  id_comp arrow := by
    ext
    · simp [Hom.comp, Hom.id]
    · simp [Hom.comp, Hom.id]
    · change
        Phi.pullback (𝟙 _) arrow.divisor +
            arrow.frobeniusDegree.val • 0 = arrow.divisor
      rw [Phi.pullback_id]
      simp
    · change
        data.rationalFunctions.pullback (𝟙 _) arrow.rationalFunction +
            arrow.frobeniusDegree.val • 0 = arrow.rationalFunction
      rw [data.rationalFunctions.pullback_id]
      simp
  comp_id arrow := by
    ext
    · simp [Hom.comp, Hom.id]
    · simp [Hom.comp, Hom.id]
    · change Phi.pullback arrow.base 0 + 1 • arrow.divisor = arrow.divisor
      rw [map_zero, zero_add, one_nsmul]
    · change
        data.rationalFunctions.pullback arrow.base 0 +
            1 • arrow.rationalFunction = arrow.rationalFunction
      rw [map_zero, zero_add, one_nsmul]
  assoc first second third := by
    ext
    · simp [Hom.comp, mul_assoc]
    · simp [Hom.comp, Category.assoc]
    · change
        Phi.pullback (first.base ≫ second.base) third.divisor +
            third.frobeniusDegree.val •
              (Phi.pullback first.base second.divisor +
                second.frobeniusDegree.val • first.divisor) =
          Phi.pullback first.base
              (Phi.pullback second.base third.divisor +
                third.frobeniusDegree.val • second.divisor) +
            (second.frobeniusDegree.val * third.frobeniusDegree.val) •
              first.divisor
      rw [Phi.pullback_comp]
      simp only [AddMonoidHom.comp_apply, map_add, map_nsmul,
        mul_nsmul, nsmul_add, add_assoc]
    · change
        data.rationalFunctions.pullback (first.base ≫ second.base)
              third.rationalFunction +
            third.frobeniusDegree.val •
              (data.rationalFunctions.pullback first.base second.rationalFunction +
                second.frobeniusDegree.val • first.rationalFunction) =
          data.rationalFunctions.pullback first.base
              (data.rationalFunctions.pullback second.base third.rationalFunction +
                third.frobeniusDegree.val • second.rationalFunction) +
            (second.frobeniusDegree.val * third.frobeniusDegree.val) •
              first.rationalFunction
      rw [data.rationalFunctions.pullback_comp]
      simp only [AddMonoidHom.comp_apply, map_add, map_nsmul,
        mul_nsmul, nsmul_add, add_assoc]

namespace Carrier

variable (Phi : DivisorialMonoidOn D IsFSM) (data : Input Phi)

@[simp]
theorem comp_frobeniusDegree
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).frobeniusDegree =
      first.frobeniusDegree * second.frobeniusDegree :=
  rfl

@[simp]
theorem comp_base
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).base = first.base ≫ second.base :=
  rfl

@[simp]
theorem comp_divisor
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).divisor =
      Phi.pullback first.base second.divisor +
        second.frobeniusDegree.val • first.divisor :=
  rfl

@[simp]
theorem comp_rationalFunction
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).rationalFunction =
      data.rationalFunctions.pullback first.base second.rationalFunction +
        second.frobeniusDegree.val • first.rationalFunction :=
  rfl

/-- Projection of model objects to the base category. -/
def base : Carrier Phi data ⥤ D where
  obj object := Object.base object
  map arrow := arrow.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The object with zero divisor class over a base object. -/
def zeroObject (data : Input Phi) (X : D) : Carrier Phi data where
  base := X
  divisorClass := 0

/-- The object associated to an effective divisor over a base object. -/
def effectiveObject (data : Input Phi) (X : D)
    (divisor : (Phi.obj X).carrier) : Carrier Phi data where
  base := X
  divisorClass := Algebra.GrothendieckAddGroup.of divisor

theorem zeroBalance (data : Input Phi) {X Y : D} (f : X ⟶ Y) :
    (1 : ℕ) • (0 : Algebra.GrothendieckAddGroup (Phi.obj X).carrier) +
        Algebra.GrothendieckAddGroup.of 0 =
      gpPullback Phi f
          (0 : Algebra.GrothendieckAddGroup (Phi.obj Y).carrier) +
        data.divisor X 0 := by
  simp

/-- Every base arrow lifts between the zero-divisor objects. -/
def zeroBaseArrow (data : Input Phi) {X Y : D} (f : X ⟶ Y) :
    Hom Phi data (zeroObject Phi data X) (zeroObject Phi data Y) where
  frobeniusDegree := 1
  base := f
  divisor := 0
  rationalFunction := 0
  balance := by
    dsimp [zeroObject]
    exact zeroBalance Phi data f

/-- Adding a localization denominator yields its numerator in the groupification. -/
theorem grothendieck_add_denominator
    (M : DivisorialAddMonoid)
    (numerator : M.carrier)
    (denominator : (⊤ : AddSubmonoid M.carrier)) :
    (AddLocalization.mk numerator denominator :
        Algebra.GrothendieckAddGroup M.carrier) +
        Algebra.GrothendieckAddGroup.of denominator.1 =
      Algebra.GrothendieckAddGroup.of numerator := by
  letI : IsLeftCancelAdd M.carrier :=
    ⟨fun a b c equality ↦ M.integral a b c equality⟩
  letI : IsCancelAdd M.carrier :=
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd M.carrier
  change
    AddLocalization.mk numerator denominator +
        AddLocalization.mk denominator.1
          (0 : (⊤ : AddSubmonoid M.carrier)) =
      AddLocalization.mk numerator
        (0 : (⊤ : AddSubmonoid M.carrier))
  rw [AddLocalization.mk_add]
  apply AddLocalization.mk_eq_mk_iff'.2
  simp only [AddSubmonoid.coe_zero, zero_add]
  simpa using (add_comm numerator denominator.1)

/-- A common negative denominator plus the left effective correction recovers
the left localization representative. -/
theorem commonLower_add_left (M : DivisorialAddMonoid)
    (leftNumerator : M.carrier)
    (leftDenominator : (⊤ : AddSubmonoid M.carrier))
    (rightDenominator : (⊤ : AddSubmonoid M.carrier)) :
    -(Algebra.GrothendieckAddGroup.of leftDenominator.1 +
        Algebra.GrothendieckAddGroup.of rightDenominator.1) +
        Algebra.GrothendieckAddGroup.of
          (leftNumerator + rightDenominator.1) =
      (AddLocalization.mk leftNumerator leftDenominator :
        Algebra.GrothendieckAddGroup M.carrier) := by
  have fraction :=
    grothendieck_add_denominator M leftNumerator leftDenominator
  rw [map_add]
  rw [← fraction]
  abel

/-- A common negative denominator plus the right effective correction recovers
the right localization representative. -/
theorem commonLower_add_right (M : DivisorialAddMonoid)
    (leftDenominator : (⊤ : AddSubmonoid M.carrier))
    (rightNumerator : M.carrier)
    (rightDenominator : (⊤ : AddSubmonoid M.carrier)) :
    -(Algebra.GrothendieckAddGroup.of leftDenominator.1 +
        Algebra.GrothendieckAddGroup.of rightDenominator.1) +
        Algebra.GrothendieckAddGroup.of
          (rightNumerator + leftDenominator.1) =
      (AddLocalization.mk rightNumerator rightDenominator :
        Algebra.GrothendieckAddGroup M.carrier) := by
  have fraction :=
    grothendieck_add_denominator M rightNumerator rightDenominator
  rw [map_add]
  rw [← fraction]
  abel

/-- Every groupification class has a numerator-denominator representative. -/
theorem localizationRepresentative {M : Type u} [AddCommMonoid M]
    (value : AddLocalization (⊤ : AddSubmonoid M)) :
    ∃ pair : M × (⊤ : AddSubmonoid M),
      value = AddLocalization.mk pair.1 pair.2 := by
  refine AddLocalization.induction_on value ?_
  intro pair
  exact ⟨pair, rfl⟩

theorem commonLeftBalance (X : D)
    (leftClass : Algebra.GrothendieckAddGroup (Phi.obj X).carrier)
    (leftNumerator : (Phi.obj X).carrier)
    (leftDenominator rightDenominator :
      (⊤ : AddSubmonoid (Phi.obj X).carrier))
    (leftClass_eq : leftClass =
      AddLocalization.mk leftNumerator leftDenominator) :
    (1 : ℕ) •
          -(Algebra.GrothendieckAddGroup.of leftDenominator.1 +
            Algebra.GrothendieckAddGroup.of rightDenominator.1) +
        Algebra.GrothendieckAddGroup.of
          (leftNumerator + rightDenominator.1) =
      gpPullback Phi (𝟙 X) leftClass + data.divisor X 0 := by
  rw [gpPullback_id]
  simp only [AddMonoidHom.id_apply, map_zero, add_zero, one_nsmul]
  rw [leftClass_eq]
  exact commonLower_add_left (Phi.obj X) leftNumerator
    leftDenominator rightDenominator

theorem commonRightBalance {X Y : D} (baseIso : X ≅ Y)
    (rightClass : Algebra.GrothendieckAddGroup (Phi.obj Y).carrier)
    (leftDenominator : (⊤ : AddSubmonoid (Phi.obj X).carrier))
    (rightNumerator : (Phi.obj X).carrier)
    (rightDenominator : (⊤ : AddSubmonoid (Phi.obj X).carrier))
    (rightClass_eq : gpPullback Phi baseIso.hom rightClass =
      AddLocalization.mk rightNumerator rightDenominator) :
    (1 : ℕ) •
          -(Algebra.GrothendieckAddGroup.of leftDenominator.1 +
            Algebra.GrothendieckAddGroup.of rightDenominator.1) +
        Algebra.GrothendieckAddGroup.of
          (rightNumerator + leftDenominator.1) =
      gpPullback Phi baseIso.hom rightClass + data.divisor X 0 := by
  simp only [map_zero, add_zero, one_nsmul]
  rw [rightClass_eq]
  exact commonLower_add_right (Phi.obj X) leftDenominator
    rightNumerator rightDenominator

/-- A localization representative gives a model arrow to its numerator. -/
def toEffectiveObject (data : Input Phi) (X : D)
    (numerator : (Phi.obj X).carrier)
    (denominator : (⊤ : AddSubmonoid (Phi.obj X).carrier)) :
    Hom Phi data
      ({ base := X
         divisorClass := AddLocalization.mk numerator denominator } :
        Carrier Phi data)
      (effectiveObject Phi data X numerator) where
  frobeniusDegree := 1
  base := 𝟙 X
  divisor := denominator.1
  rationalFunction := 0
  balance := by
    dsimp [effectiveObject]
    simp only [map_zero, add_zero]
    rw [gpPullback_id]
    change (1 : ℕ) •
        (AddLocalization.mk numerator denominator :
          Algebra.GrothendieckAddGroup (Phi.obj X).carrier) +
          Algebra.GrothendieckAddGroup.of denominator.1 =
        Algebra.GrothendieckAddGroup.of numerator
    rw [one_nsmul]
    exact grothendieck_add_denominator (Phi.obj X) numerator denominator

/-- The zero object maps to every effective divisor object over the same base. -/
def zeroToEffectiveObject (data : Input Phi) (X : D)
    (divisor : (Phi.obj X).carrier) :
    Hom Phi data (zeroObject Phi data X)
      (effectiveObject Phi data X divisor) where
  frobeniusDegree := 1
  base := 𝟙 X
  divisor := divisor
  rationalFunction := 0
  balance := by
    dsimp [zeroObject, effectiveObject]
    change (1 : ℕ) •
        (0 : Algebra.GrothendieckAddGroup (Phi.obj X).carrier) +
          Algebra.GrothendieckAddGroup.of divisor =
        gpPullback Phi (𝟙 X)
            (Algebra.GrothendieckAddGroup.of divisor) +
          data.divisor X 0
    rw [gpPullback_id]
    norm_num

theorem value_eq_zeroObject
    {alpha : Type u} (F : Carrier Phi data → alpha)
    (preserves : ∀ {source target : Carrier Phi data}
      (_ : Hom Phi data source target), F source = F target)
    (object : Carrier Phi data) :
    F object = F (zeroObject Phi data (Object.base object)) := by
  rcases object with ⟨X, divisorClass⟩
  refine AddLocalization.induction_on divisorClass ?_
  rintro ⟨numerator, denominator⟩
  exact (preserves
      (toEffectiveObject Phi data X numerator denominator)).trans
    (preserves (zeroToEffectiveObject Phi data X numerator)).symm

/-- The model carrier is connected whenever the base category is connected. -/
theorem isConnected [IsConnected D] :
    @IsConnected (Carrier Phi data) (carrierCategory Phi data) := by
  letI : Nonempty (Carrier Phi data) :=
    ⟨zeroObject Phi data (Classical.arbitrary D)⟩
  apply IsConnected.of_constant_of_preserves_morphisms
  intro alpha F preserves first second
  calc
    F first = F (zeroObject Phi data (Object.base first)) :=
      value_eq_zeroObject Phi data F preserves first
    _ = F (zeroObject Phi data (Object.base second)) := by
      apply CategoryTheory.constant_of_preserves_morphisms
        (fun X : D ↦ F (zeroObject Phi data X))
      intro X Y f
      exact preserves (zeroBaseArrow Phi data f)
    _ = F second :=
      (value_eq_zeroObject Phi data F preserves second).symm

/-- Every model arrow is epic when the base category is totally epimorphic. -/
theorem epi
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : Carrier Phi data}
    (arrow : source ⟶ target) : Epi arrow := by
  constructor
  intro next first second equality
  letI : Epi arrow.base := baseTotallyEpimorphic arrow.base
  have degreeEquality :
      first.frobeniusDegree = second.frobeniusDegree := by
    have projected := congrArg Hom.frobeniusDegree equality
    change
      arrow.frobeniusDegree * first.frobeniusDegree =
        arrow.frobeniusDegree * second.frobeniusDegree at projected
    exact mul_left_cancel projected
  have baseEquality : first.base = second.base := by
    have projected := congrArg Hom.base equality
    change arrow.base ≫ first.base = arrow.base ≫ second.base at projected
    exact (cancel_epi arrow.base).mp projected
  have divisorEquality : first.divisor = second.divisor := by
    have projected := congrArg Hom.divisor equality
    change
      Phi.pullback arrow.base first.divisor +
          first.frobeniusDegree.val • arrow.divisor =
        Phi.pullback arrow.base second.divisor +
          second.frobeniusDegree.val • arrow.divisor at projected
    rw [degreeEquality] at projected
    apply Phi.characteristicallyInjective arrow.base
    have cancellable :
        second.frobeniusDegree.val • arrow.divisor +
            Phi.pullback arrow.base first.divisor =
          second.frobeniusDegree.val • arrow.divisor +
            Phi.pullback arrow.base second.divisor := by
      rw [add_comm (second.frobeniusDegree.val • arrow.divisor),
        add_comm (second.frobeniusDegree.val • arrow.divisor)]
      exact projected
    exact (Phi.obj (Object.base source)).integral
      (second.frobeniusDegree.val • arrow.divisor)
      (Phi.pullback arrow.base first.divisor)
      (Phi.pullback arrow.base second.divisor)
      cancellable
  have rationalFunctionEquality :
      first.rationalFunction = second.rationalFunction := by
    have projected := congrArg Hom.rationalFunction equality
    change
      data.rationalFunctions.pullback arrow.base first.rationalFunction +
          first.frobeniusDegree.val • arrow.rationalFunction =
        data.rationalFunctions.pullback arrow.base second.rationalFunction +
          second.frobeniusDegree.val • arrow.rationalFunction at projected
    rw [degreeEquality] at projected
    apply data.rationalFunctions.pullback_injective arrow.base
    exact add_right_cancel projected
  exact Hom.ext degreeEquality baseEquality divisorEquality
    rationalFunctionEquality

/-- The structure functor to the elementary Frobenioid, forgetting `u_phi`. -/
def structureFunctor :
    @Functor (Carrier Phi data) (carrierCategory Phi data)
      (ElementaryFrobenioid D IsFSM Phi)
      (ElementaryFrobenioid.instCategory Phi) where
  obj object :=
    show ElementaryFrobenioid D IsFSM Phi from
      @Object.base D categoryD IsFSM Phi object
  map arrow :=
    { base := arrow.base
      divisor := arrow.divisor
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The model category with its literal pre-Frobenioid structure. -/
def preFrobenioid : PreFrobenioid (Carrier Phi data) D IsFSM where
  divisorMonoid := Phi
  structureFunctor := structureFunctor Phi data

/-- Definition 1.3(i)(b): any two objects over isomorphic base objects admit
a common source through pre-steps inducing the prescribed base isomorphism. -/
theorem commonPreSteps
    (left right : Carrier Phi data)
    (baseIso : (preFrobenioid Phi data).base.obj left ≅
      (preFrobenioid Phi data).base.obj right) :
    Nonempty ((preFrobenioid Phi data).CommonPreStepWitness
      left right baseIso) := by
  let X := Object.base left
  let Y := Object.base right
  change X ≅ Y at baseIso
  rcases localizationRepresentative left.divisorClass with
    ⟨⟨leftNumerator, leftDenominator⟩, leftClass_eq⟩
  rcases localizationRepresentative
      (gpPullback Phi baseIso.hom right.divisorClass) with
    ⟨⟨rightNumerator, rightDenominator⟩, rightClass_eq⟩
  let midpoint : Carrier Phi data :=
    { base := X
      divisorClass :=
        -(Algebra.GrothendieckAddGroup.of leftDenominator.1 +
          Algebra.GrothendieckAddGroup.of rightDenominator.1) }
  let toLeft : Hom Phi data midpoint left :=
    { frobeniusDegree := 1
      base := 𝟙 X
      divisor := leftNumerator + rightDenominator.1
      rationalFunction := 0
      balance := by
        change (1 : ℕ) •
              -(Algebra.GrothendieckAddGroup.of leftDenominator.1 +
                Algebra.GrothendieckAddGroup.of rightDenominator.1) +
            Algebra.GrothendieckAddGroup.of
              (leftNumerator + rightDenominator.1) =
          gpPullback Phi (𝟙 X) left.divisorClass + data.divisor X 0
        exact commonLeftBalance Phi data X left.divisorClass leftNumerator
          leftDenominator rightDenominator leftClass_eq }
  let toRight : Hom Phi data midpoint right :=
    { frobeniusDegree := 1
      base := baseIso.hom
      divisor := rightNumerator + leftDenominator.1
      rationalFunction := 0
      balance := by
        change (1 : ℕ) •
              -(Algebra.GrothendieckAddGroup.of leftDenominator.1 +
                Algebra.GrothendieckAddGroup.of rightDenominator.1) +
            Algebra.GrothendieckAddGroup.of
              (rightNumerator + leftDenominator.1) =
          gpPullback Phi baseIso.hom right.divisorClass + data.divisor X 0
        exact commonRightBalance Phi data baseIso right.divisorClass
          leftDenominator rightNumerator rightDenominator rightClass_eq }
  refine ⟨
    { midpoint := midpoint
      toLeft := toLeft
      toRight := toRight
      toLeft_preStep := ?_
      toRight_preStep := ?_
      leftBaseInverse := 𝟙 X
      leftBaseInverse_hom := by
        change 𝟙 X ≫ 𝟙 X = 𝟙 X
        simp
      hom_leftBaseInverse := by
        change 𝟙 X ≫ 𝟙 X = 𝟙 X
        simp
      comparison := by
        change 𝟙 X ≫ baseIso.hom = baseIso.hom
        simp }⟩
  · constructor
    · rfl
    · change IsIso (𝟙 X)
      infer_instance
  · constructor
    · rfl
    · change IsIso baseIso.hom
      infer_instance

theorem pullbackComparisonTarget_ext
    {source target test : Carrier Phi data}
    {arrow : Hom Phi data source target}
    {left right : (preFrobenioid Phi data).PullbackComparisonTarget
      arrow test}
    (toCodomain : left.toCodomain = right.toCodomain)
    (toBaseDomain : left.toBaseDomain = right.toBaseDomain) :
    left = right := by
  cases left
  cases right
  cases toCodomain
  cases toBaseDomain
  rfl

/-- The literal pullback of a model object along a base arrow. -/
def pullbackObject (target : Carrier Phi data) {X : D}
    (f : X ⟶ Object.base target) : Carrier Phi data where
  base := X
  divisorClass := gpPullback Phi f target.divisorClass

/-- The canonical model arrow from a literal pullback object. -/
def pullbackArrow (target : Carrier Phi data) {X : D}
    (f : X ⟶ Object.base target) :
    Hom Phi data (pullbackObject Phi data target f) target where
  frobeniusDegree := 1
  base := f
  divisor := 0
  rationalFunction := 0
  balance := by
    dsimp only [pullbackObject]
    change (1 : ℕ) • gpPullback Phi f target.divisorClass +
        Algebra.GrothendieckAddGroup.of
          (0 : (Phi.obj X).carrier) =
      gpPullback Phi f target.divisorClass + data.divisor X 0
    simp only [map_zero, add_zero, one_nsmul]

/-- The canonical model arrow realizes the representable-functor pullback
over its base arrow, as required by Definition 1.2(ii). -/
theorem pullbackArrow_isPullback (target : Carrier Phi data) {X : D}
    (f : X ⟶ Object.base target) :
    (preFrobenioid Phi data).IsPullback
      (pullbackArrow Phi data target f) := by
  intro test
  constructor
  · intro left right equality
    have compositeEquality :
        left ≫ pullbackArrow Phi data target f =
          right ≫ pullbackArrow Phi data target f :=
      congrArg
        PreFrobenioid.PullbackComparisonTarget.toCodomain equality
    have baseEquality : left.base = right.base :=
      congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain equality
    have degreeEquality :
        left.frobeniusDegree = right.frobeniusDegree := by
      have projected := congrArg Hom.frobeniusDegree compositeEquality
      change left.frobeniusDegree * 1 = right.frobeniusDegree * 1 at projected
      simpa using projected
    have divisorEquality : left.divisor = right.divisor := by
      have projected := congrArg Hom.divisor compositeEquality
      change Phi.pullback left.base 0 + 1 • left.divisor =
        Phi.pullback right.base 0 + 1 • right.divisor at projected
      rw [one_nsmul, one_nsmul] at projected
      simpa using projected
    have rationalFunctionEquality :
        left.rationalFunction = right.rationalFunction := by
      have projected := congrArg Hom.rationalFunction compositeEquality
      change data.rationalFunctions.pullback left.base 0 +
          1 • left.rationalFunction =
        data.rationalFunctions.pullback right.base 0 +
          1 • right.rationalFunction at projected
      rw [one_nsmul, one_nsmul] at projected
      simpa using projected
    exact Hom.ext degreeEquality baseEquality divisorEquality
      rationalFunctionEquality
  · intro comparison
    let lift : Hom Phi data test (pullbackObject Phi data target f) :=
      { frobeniusDegree := comparison.toCodomain.frobeniusDegree
        base := comparison.toBaseDomain
        divisor := comparison.toCodomain.divisor
        rationalFunction := comparison.toCodomain.rationalFunction
        balance := by
          dsimp only [pullbackObject]
          change _ =
            ((gpPullback Phi comparison.toBaseDomain).comp
                (gpPullback Phi f)) target.divisorClass + _
          rw [← gpPullback_comp]
          have baseCommutes := comparison.commutes
          change comparison.toCodomain.base =
            comparison.toBaseDomain ≫ f at baseCommutes
          rw [← baseCommutes]
          exact comparison.toCodomain.balance }
    refine ⟨lift, ?_⟩
    apply pullbackComparisonTarget_ext Phi data
    · change lift ≫ pullbackArrow Phi data target f =
        comparison.toCodomain
      apply Hom.ext
      · simp [lift, pullbackArrow]
      · exact comparison.commutes.symm
      · rw [comp_divisor Phi data lift
          (pullbackArrow Phi data target f)]
        simp only [lift, pullbackArrow, map_zero, zero_add]
        have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
        rw [degreeOne, one_nsmul]
      · rw [comp_rationalFunction Phi data lift
          (pullbackArrow Phi data target f)]
        simp only [lift, pullbackArrow, map_zero, zero_add]
        have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
        rw [degreeOne, one_nsmul]
    · rfl

theorem pullbackSliceHom_ext {target : Carrier Phi data}
    {leftObject rightObject :
      PreFrobenioid.PullbackSliceObject target}
    {left right : PreFrobenioid.PullbackSliceHom
      leftObject rightObject}
    (hom : left.hom = right.hom) : left = right := by
  cases left
  cases right
  cases hom
  rfl

theorem baseSliceHom_ext {target : Carrier Phi data}
    {leftObject rightObject :
      (preFrobenioid Phi data).BaseSliceObject target}
    {left right : (preFrobenioid Phi data).BaseSliceHom
      leftObject rightObject}
    (hom : left.hom = right.hom) : left = right := by
  cases left
  cases right
  cases hom
  rfl

/-- Projection from pullback slices is fully faithful because the codomain
pullback arrow has its representable universal property. -/
theorem pullbackSliceProjection_bijective
    {target : Carrier Phi data}
    (leftObject rightObject :
      PreFrobenioid.PullbackSliceObject target)
    (rightPullback :
      (preFrobenioid Phi data).IsPullback rightObject.hom) :
    Function.Bijective
      (fun f : PreFrobenioid.PullbackSliceHom
          leftObject rightObject ↦
        PreFrobenioid.PullbackSliceHom.toBase
          (preFrobenioid Phi data) f) := by
  constructor
  · intro left right baseEquality
    apply pullbackSliceHom_ext Phi data
    apply (rightPullback leftObject.source).1
    apply pullbackComparisonTarget_ext Phi data
    · change left.hom ≫ rightObject.hom =
          right.hom ≫ rightObject.hom
      rw [left.commutes, right.commutes]
    · exact congrArg PreFrobenioid.BaseSliceHom.hom baseEquality
  · intro baseMap
    let comparison :
        (preFrobenioid Phi data).PullbackComparisonTarget
          rightObject.hom leftObject.source :=
      { toCodomain := leftObject.hom
        toBaseDomain := baseMap.hom
        commutes := by
          exact baseMap.commutes.symm }
    rcases (rightPullback leftObject.source).2 comparison with
      ⟨hom, homComparison⟩
    have commutes := congrArg
      PreFrobenioid.PullbackComparisonTarget.toCodomain homComparison
    change hom ≫ rightObject.hom = leftObject.hom at commutes
    let lift : PreFrobenioid.PullbackSliceHom
        leftObject rightObject :=
      { hom := hom
        commutes := commutes }
    refine ⟨lift, ?_⟩
    apply baseSliceHom_ext Phi data
    exact congrArg
      PreFrobenioid.PullbackComparisonTarget.toBaseDomain homComparison

/-- Definition 1.3(i)(c): pullback arrows over a model object form a category
equivalent to the base slice over that object's base. -/
theorem pullbackBaseSlices (target : Carrier Phi data) :
    (preFrobenioid Phi data).PullbackBaseSliceEquivalence target where
  essentiallySurjective baseObject := by
    let sliceObject :
        PreFrobenioid.PullbackSliceObject target :=
      { source := pullbackObject Phi data target baseObject.hom
        hom := pullbackArrow Phi data target baseObject.hom }
    refine ⟨sliceObject,
      pullbackArrow_isPullback Phi data target baseObject.hom, ⟨?_⟩⟩
    refine
      { iso := Iso.refl baseObject.source
        hom_commutes := ?_ }
    change 𝟙 baseObject.source ≫ baseObject.hom = baseObject.hom
    simp
  fullyFaithful leftObject rightObject _ rightPullback :=
    pullbackSliceProjection_bijective Phi data leftObject rightObject
      rightPullback

/--
The explicit inverse to a linear, base-isomorphic, isometric model arrow.
Its rational-function component is the negative pullback of the original one.
-/
def inverseOfPreStepIsometric
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (linear : (preFrobenioid Phi data).IsLinear arrow)
    (baseIso : (preFrobenioid Phi data).IsBaseIso arrow)
    (isometric : (preFrobenioid Phi data).IsIsometric arrow) :
    target ⟶ source := by
  change IsIso arrow.base at baseIso
  letI : IsIso arrow.base := baseIso
  refine
    { frobeniusDegree := 1
      base := inv arrow.base
      divisor := 0
      rationalFunction :=
        -data.rationalFunctions.pullback (inv arrow.base)
          arrow.rationalFunction
      balance := ?_ }
  change arrow.frobeniusDegree = 1 at linear
  change arrow.divisor = 0 at isometric
  have source_eq :
      source.divisorClass =
        gpPullback Phi arrow.base target.divisorClass +
          data.divisor (Object.base source) arrow.rationalFunction := by
    have sourceBalance := arrow.balance
    rw [linear, isometric] at sourceBalance
    rw [map_zero, add_zero] at sourceBalance
    change (1 : ℕ) • source.divisorClass =
      gpPullback Phi arrow.base target.divisorClass +
        data.divisor (Object.base source) arrow.rationalFunction at sourceBalance
    rw [one_nsmul] at sourceBalance
    exact sourceBalance
  have pulled := congrArg (gpPullback Phi (inv arrow.base)) source_eq
  simp only [map_add] at pulled
  have gpCancel :
      gpPullback Phi (inv arrow.base)
          (gpPullback Phi arrow.base target.divisorClass) =
        target.divisorClass := by
    rw [← AddMonoidHom.comp_apply, ← gpPullback_comp,
      IsIso.inv_hom_id, gpPullback_id]
    rfl
  rw [gpCancel] at pulled
  norm_num
  change (1 : ℕ) • target.divisorClass =
    gpPullback Phi (inv arrow.base) source.divisorClass -
      data.divisor (Object.base target)
        (data.rationalFunctions.pullback (inv arrow.base)
          arrow.rationalFunction)
  rw [one_nsmul, data.divisor_natural, pulled]
  abel

/-- An isometric pre-step in the model category is an isomorphism. -/
theorem isIso_of_preStep_isometric
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow)
    (isometric : (preFrobenioid Phi data).IsIsometric arrow) :
    IsIso arrow := by
  rcases preStep with ⟨linear, baseIso⟩
  change arrow.frobeniusDegree = 1 at linear
  change IsIso arrow.base at baseIso
  change arrow.divisor = 0 at isometric
  letI : IsIso arrow.base := baseIso
  let inverse :=
    inverseOfPreStepIsometric Phi data arrow linear baseIso isometric
  have inverse_degree : inverse.frobeniusDegree = 1 := rfl
  have inverse_base : inverse.base = inv arrow.base := rfl
  have inverse_divisor : inverse.divisor = 0 := rfl
  have inverse_rationalFunction : inverse.rationalFunction =
      -data.rationalFunctions.pullback (inv arrow.base)
        arrow.rationalFunction := rfl
  apply IsIso.mk
  refine ⟨inverse, ?_, ?_⟩
  · apply Hom.ext
    · rw [comp_frobeniusDegree, inverse_degree, linear]
      rfl
    · rw [comp_base, inverse_base]
      change arrow.base ≫ inv arrow.base = 𝟙 (Object.base source)
      exact IsIso.hom_inv_id arrow.base
    · rw [comp_divisor, inverse_divisor, inverse_degree, isometric]
      simp only [map_zero, PNat.val_ofNat, nsmul_zero, add_zero]
      change (0 : (Phi.obj (Object.base source)).carrier) = 0
      rfl
    · rw [comp_rationalFunction, inverse_rationalFunction, inverse_degree]
      change
        data.rationalFunctions.pullback arrow.base
              (-data.rationalFunctions.pullback (inv arrow.base)
                arrow.rationalFunction) +
            1 • arrow.rationalFunction = 0
      rw [map_neg]
      have pullbackCancel :
          data.rationalFunctions.pullback arrow.base
              (data.rationalFunctions.pullback (inv arrow.base)
                arrow.rationalFunction) =
            arrow.rationalFunction := by
        rw [← AddMonoidHom.comp_apply,
          ← data.rationalFunctions.pullback_comp,
          IsIso.hom_inv_id, data.rationalFunctions.pullback_id]
        rfl
      rw [pullbackCancel]
      simp only [one_nsmul, neg_add_cancel]
  · apply Hom.ext
    · rw [comp_frobeniusDegree, inverse_degree, linear]
      rfl
    · rw [comp_base, inverse_base]
      change inv arrow.base ≫ arrow.base = 𝟙 (Object.base target)
      exact IsIso.inv_hom_id arrow.base
    · rw [comp_divisor, inverse_divisor, inverse_base, linear,
        isometric]
      simp only [map_zero, PNat.val_ofNat, nsmul_zero, add_zero]
      change (0 : (Phi.obj (Object.base target)).carrier) = 0
      rfl
    · rw [comp_rationalFunction, inverse_rationalFunction,
        inverse_base, linear]
      change
        data.rationalFunctions.pullback (inv arrow.base)
              arrow.rationalFunction +
            (1 : ℕ) •
              (-data.rationalFunctions.pullback (inv arrow.base)
                arrow.rationalFunction) = 0
      rw [one_nsmul]
      exact add_neg_cancel _

/-- Every object of the model Frobenioid is isotropic. -/
theorem isIsotropic (object : Carrier Phi data) :
    (preFrobenioid Phi data).IsIsotropic object := by
  intro target arrow preStep isometric
  exact isIso_of_preStep_isometric Phi data arrow preStep isometric

/-- Every model arrow is co-angular because every model object is isotropic. -/
theorem isCoAngular {source target : Carrier Phi data}
    (arrow : source ⟶ target) :
    (preFrobenioid Phi data).IsCoAngular arrow := by
  intro U V gamma beta alpha _ _ betaPreStep betaIsometric _
  exact isIso_of_preStep_isometric Phi data beta betaPreStep betaIsometric

/-- In the model category, LB-invertibility is exactly isometry. -/
theorem isLBInvertible_iff {source target : Carrier Phi data}
    (arrow : source ⟶ target) :
    (preFrobenioid Phi data).IsLBInvertible arrow ↔
      (preFrobenioid Phi data).IsIsometric arrow := by
  constructor
  · exact fun hypothesis ↦ hypothesis.2
  · exact fun hypothesis ↦ ⟨isCoAngular Phi data arrow, hypothesis⟩

/--
The paper's explicit description of Frobenius-type arrows in the isotropic
model category: zero divisor and base-isomorphic projection.
-/
theorem isOfFrobeniusType_iff {source target : Carrier Phi data}
    (arrow : source ⟶ target) :
    (preFrobenioid Phi data).IsOfFrobeniusType arrow ↔
      (preFrobenioid Phi data).IsIsometric arrow ∧
        (preFrobenioid Phi data).IsBaseIso arrow := by
  rw [PreFrobenioid.IsOfFrobeniusType, isLBInvertible_iff Phi data]

theorem endomorphism_divisor_eq
    {object : Carrier Phi data}
    (alpha : (preFrobenioid Phi data).LinearBaseIdentityEndomorphism
      object) :
    Algebra.GrothendieckAddGroup.of alpha.hom.divisor =
      data.divisor (Object.base object) alpha.hom.rationalFunction := by
  have balance := alpha.hom.balance
  have linear := alpha.linear
  change alpha.hom.frobeniusDegree = 1 at linear
  have baseIdentity := alpha.baseIdentity
  change alpha.hom.base = 𝟙 (Object.base object) at baseIdentity
  rw [linear, baseIdentity, gpPullback_id] at balance
  simp only [AddMonoidHom.id_apply] at balance
  have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
  rw [degreeOne, one_nsmul] at balance
  exact add_left_cancel balance

/-- Pull a base-identity linear endomorphism through a base isomorphism. -/
def baseIsoTransport
    {source target : Carrier Phi data}
    (baseIso : Object.base source ≅ Object.base target)
    (alpha : (preFrobenioid Phi data).LinearBaseIdentityEndomorphism
      source) :
    (preFrobenioid Phi data).LinearBaseIdentityEndomorphism target where
  hom :=
    { frobeniusDegree := 1
      base := 𝟙 (Object.base target)
      divisor := Phi.pullback baseIso.inv alpha.hom.divisor
      rationalFunction :=
        data.rationalFunctions.pullback baseIso.inv
          alpha.hom.rationalFunction
      balance := by
        change (1 : ℕ) • target.divisorClass +
              Algebra.GrothendieckAddGroup.of
                (Phi.pullback baseIso.inv alpha.hom.divisor) =
            gpPullback Phi (𝟙 (Object.base target))
                target.divisorClass +
              data.divisor (Object.base target)
                (data.rationalFunctions.pullback baseIso.inv
                  alpha.hom.rationalFunction)
        rw [one_nsmul, gpPullback_id]
        simp only [AddMonoidHom.id_apply]
        have pulled := congrArg (gpPullback Phi baseIso.inv)
          (endomorphism_divisor_eq Phi data alpha)
        rw [gpPullback_of, ← data.divisor_natural] at pulled
        rw [pulled] }
  linear := rfl
  baseIdentity := rfl

theorem baseIsoTransport_one
    {source target : Carrier Phi data}
    (baseIso : Object.base source ≅ Object.base target) :
    baseIsoTransport Phi data baseIso
        (1 : (preFrobenioid Phi data).LinearBaseIdentityEndomorphism
          source) =
      (1 : (preFrobenioid Phi data).LinearBaseIdentityEndomorphism
        target) := by
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · rfl
  · rfl
  · change Phi.pullback baseIso.inv 0 = 0
    exact map_zero _
  · change data.rationalFunctions.pullback baseIso.inv 0 = 0
    exact map_zero _

theorem baseIsoTransport_mul
    {source target : Carrier Phi data}
    (baseIso : Object.base source ≅ Object.base target)
    (alpha beta :
      (preFrobenioid Phi data).LinearBaseIdentityEndomorphism source) :
    baseIsoTransport Phi data baseIso (alpha * beta) =
      baseIsoTransport Phi data baseIso alpha *
        baseIsoTransport Phi data baseIso beta := by
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · change (1 : ℕ+) = 1 * 1
    rfl
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp
  · change Phi.pullback baseIso.inv
          (Phi.pullback alpha.hom.base beta.hom.divisor +
            beta.hom.frobeniusDegree.val • alpha.hom.divisor) =
        Phi.pullback (𝟙 (Object.base target))
            (Phi.pullback baseIso.inv beta.hom.divisor) +
          (1 : ℕ+).val •
            Phi.pullback baseIso.inv alpha.hom.divisor
    have alphaBase := alpha.baseIdentity
    change alpha.hom.base = 𝟙 (Object.base source) at alphaBase
    have betaLinear := beta.linear
    change beta.hom.frobeniusDegree = 1 at betaLinear
    rw [alphaBase, betaLinear, Phi.pullback_id]
    rw [Phi.pullback_id]
    simp only [AddMonoidHom.id_apply, map_add]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    abel
  · change data.rationalFunctions.pullback baseIso.inv
          (data.rationalFunctions.pullback alpha.hom.base
              beta.hom.rationalFunction +
            beta.hom.frobeniusDegree.val •
              alpha.hom.rationalFunction) =
        data.rationalFunctions.pullback (𝟙 (Object.base target))
            (data.rationalFunctions.pullback baseIso.inv
              beta.hom.rationalFunction) +
          (1 : ℕ+).val •
            data.rationalFunctions.pullback baseIso.inv
              alpha.hom.rationalFunction
    have alphaBase := alpha.baseIdentity
    change alpha.hom.base = 𝟙 (Object.base source) at alphaBase
    have betaLinear := beta.linear
    change beta.hom.frobeniusDegree = 1 at betaLinear
    rw [alphaBase, betaLinear, data.rationalFunctions.pullback_id]
    rw [data.rationalFunctions.pullback_id]
    simp only [AddMonoidHom.id_apply, map_add]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    abel

def baseIsoTransportHom
    {source target : Carrier Phi data}
    (baseIso : Object.base source ≅ Object.base target) :
    (preFrobenioid Phi data).LinearBaseIdentityEndomorphism source →*
      (preFrobenioid Phi data).LinearBaseIdentityEndomorphism target where
  toFun := baseIsoTransport Phi data baseIso
  map_one' := baseIsoTransport_one Phi data baseIso
  map_mul' := baseIsoTransport_mul Phi data baseIso

theorem baseIsoTransport_symm_apply
    {source target : Carrier Phi data}
    (baseIso : Object.base source ≅ Object.base target)
    (alpha : (preFrobenioid Phi data).LinearBaseIdentityEndomorphism
      source) :
    baseIsoTransport Phi data baseIso.symm
        (baseIsoTransport Phi data baseIso alpha) = alpha := by
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · exact alpha.linear.symm
  · exact alpha.baseIdentity.symm
  · change Phi.pullback baseIso.hom
        (Phi.pullback baseIso.inv alpha.hom.divisor) = alpha.hom.divisor
    rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
      baseIso.hom_inv_id, Phi.pullback_id]
    rfl
  · change data.rationalFunctions.pullback baseIso.hom
        (data.rationalFunctions.pullback baseIso.inv
          alpha.hom.rationalFunction) = alpha.hom.rationalFunction
    rw [← AddMonoidHom.comp_apply,
      ← data.rationalFunctions.pullback_comp,
      baseIso.hom_inv_id, data.rationalFunctions.pullback_id]
    rfl

/-- The model's literal monoid isomorphism on `O^bullet` induced by a base
isomorphism. -/
def baseIsoTransportEquiv
    {source target : Carrier Phi data}
    (baseIso : Object.base source ≅ Object.base target) :
    (preFrobenioid Phi data).LinearBaseIdentityEndomorphism source ≃*
      (preFrobenioid Phi data).LinearBaseIdentityEndomorphism target where
  toFun := baseIsoTransport Phi data baseIso
  invFun := baseIsoTransport Phi data baseIso.symm
  left_inv := baseIsoTransport_symm_apply Phi data baseIso
  right_inv := baseIsoTransport_symm_apply Phi data baseIso.symm
  map_mul' := baseIsoTransport_mul Phi data baseIso

theorem baseIsoTransport_conjugates
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (linear : (preFrobenioid Phi data).IsLinear arrow)
    (baseIsIso : IsIso arrow.base)
    (alpha : (preFrobenioid Phi data).LinearBaseIdentityEndomorphism
      source) :
    alpha.hom ≫ arrow =
      arrow ≫ (baseIsoTransport Phi data (asIso arrow.base) alpha).hom := by
  letI : IsIso arrow.base := baseIsIso
  have arrowLinear := linear
  change arrow.frobeniusDegree = 1 at arrowLinear
  have alphaLinear := alpha.linear
  change alpha.hom.frobeniusDegree = 1 at alphaLinear
  have alphaBase := alpha.baseIdentity
  change alpha.hom.base = 𝟙 (Object.base source) at alphaBase
  apply Hom.ext
  · rw [comp_frobeniusDegree, comp_frobeniusDegree,
      alphaLinear, arrowLinear]
    rfl
  · rw [comp_base, comp_base, alphaBase]
    change 𝟙 _ ≫ arrow.base = arrow.base ≫ 𝟙 _
    simp
  · rw [comp_divisor, comp_divisor]
    change Phi.pullback alpha.hom.base arrow.divisor +
          arrow.frobeniusDegree.val • alpha.hom.divisor =
        Phi.pullback arrow.base
            (Phi.pullback (inv arrow.base) alpha.hom.divisor) +
          (1 : ℕ+).val • arrow.divisor
    have pullbackCancel :
        Phi.pullback arrow.base
            (Phi.pullback (inv arrow.base) alpha.hom.divisor) =
          alpha.hom.divisor := by
      rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
        IsIso.hom_inv_id, Phi.pullback_id]
      rfl
    rw [alphaBase, arrowLinear, Phi.pullback_id, pullbackCancel]
    simp only [AddMonoidHom.id_apply]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    abel
  · rw [comp_rationalFunction, comp_rationalFunction]
    change data.rationalFunctions.pullback alpha.hom.base
            arrow.rationalFunction +
          arrow.frobeniusDegree.val • alpha.hom.rationalFunction =
        data.rationalFunctions.pullback arrow.base
            (data.rationalFunctions.pullback (inv arrow.base)
              alpha.hom.rationalFunction) +
          (1 : ℕ+).val • arrow.rationalFunction
    have pullbackCancel :
        data.rationalFunctions.pullback arrow.base
            (data.rationalFunctions.pullback (inv arrow.base)
              alpha.hom.rationalFunction) =
          alpha.hom.rationalFunction := by
      rw [← AddMonoidHom.comp_apply,
        ← data.rationalFunctions.pullback_comp,
        IsIso.hom_inv_id, data.rationalFunctions.pullback_id]
      rfl
    rw [alphaBase, arrowLinear,
      data.rationalFunctions.pullback_id, pullbackCancel]
    simp only [AddMonoidHom.id_apply]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    abel

def preStepBaseIso
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    Object.base source ≅ Object.base target := by
  have baseIsIso := preStep.2
  change IsIso arrow.base at baseIsIso
  letI : IsIso arrow.base := baseIsIso
  exact asIso arrow.base

/-- Definition 1.3(iii)(c)'s transport for a model co-angular pre-step. -/
def unitTransport
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    (preFrobenioid Phi data).CoAngularUnitTransport arrow where
  transport := baseIsoTransportEquiv Phi data
    (preStepBaseIso Phi data arrow preStep)
  conjugates alpha := by
    have linear := preStep.1
    have baseIsIso := preStep.2
    change IsIso arrow.base at baseIsIso
    letI : IsIso arrow.base := baseIsIso
    exact baseIsoTransport_conjugates Phi data arrow linear baseIsIso alpha

theorem endomorphism_eq_of_comp_eq
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (left right :
      (preFrobenioid Phi data).LinearBaseIdentityEndomorphism target)
    (equality : arrow ≫ left.hom = arrow ≫ right.hom) :
    left = right := by
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · exact left.linear.trans right.linear.symm
  · exact left.baseIdentity.trans right.baseIdentity.symm
  · have projected := congrArg Hom.divisor equality
    change Phi.pullback arrow.base left.hom.divisor +
          left.hom.frobeniusDegree.val • arrow.divisor =
        Phi.pullback arrow.base right.hom.divisor +
          right.hom.frobeniusDegree.val • arrow.divisor at projected
    have leftLinear := left.linear
    change left.hom.frobeniusDegree = 1 at leftLinear
    have rightLinear := right.linear
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftLinear, rightLinear] at projected
    apply Phi.characteristicallyInjective arrow.base
    have cancellable :
        (1 : ℕ+).val • arrow.divisor +
            Phi.pullback arrow.base left.hom.divisor =
          (1 : ℕ+).val • arrow.divisor +
            Phi.pullback arrow.base right.hom.divisor := by
      simpa only [add_comm] using projected
    exact (Phi.obj (Object.base source)).integral
      ((1 : ℕ+).val • arrow.divisor)
      (Phi.pullback arrow.base left.hom.divisor)
      (Phi.pullback arrow.base right.hom.divisor) cancellable
  · have projected := congrArg Hom.rationalFunction equality
    change data.rationalFunctions.pullback arrow.base
            left.hom.rationalFunction +
          left.hom.frobeniusDegree.val • arrow.rationalFunction =
        data.rationalFunctions.pullback arrow.base
            right.hom.rationalFunction +
          right.hom.frobeniusDegree.val • arrow.rationalFunction at projected
    have leftLinear := left.linear
    change left.hom.frobeniusDegree = 1 at leftLinear
    have rightLinear := right.linear
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftLinear, rightLinear] at projected
    apply data.rationalFunctions.pullback_injective arrow.base
    exact add_right_cancel projected

theorem coAngularUnitTransport_ext
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    {left right : (preFrobenioid Phi data).CoAngularUnitTransport arrow}
    (transport : left.transport = right.transport) : left = right := by
  cases left
  cases right
  cases transport
  rfl

/-- The conjugation equation uniquely determines unit transport in the model. -/
theorem unitTransport_unique
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (left right : (preFrobenioid Phi data).CoAngularUnitTransport arrow) :
    left = right := by
  apply coAngularUnitTransport_ext Phi data
  apply MulEquiv.ext
  intro alpha
  apply endomorphism_eq_of_comp_eq Phi data arrow
  exact (left.conjugates alpha).symm.trans (right.conjugates alpha)

/-- The model transport depends only on the projected base isomorphism. -/
theorem unitTransport_dependsOnlyOnBase
    {source target : Carrier Phi data} (left right : source ⟶ target)
    (leftPreStep : (preFrobenioid Phi data).IsPreStep left)
    (rightPreStep : (preFrobenioid Phi data).IsPreStep right)
    (baseEquality : left.base = right.base) :
    (unitTransport Phi data left leftPreStep).transport =
      (unitTransport Phi data right rightPreStep).transport := by
  change baseIsoTransportEquiv Phi data
      (preStepBaseIso Phi data left leftPreStep) =
    baseIsoTransportEquiv Phi data
      (preStepBaseIso Phi data right rightPreStep)
  congr 1
  apply Iso.ext
  exact baseEquality

theorem zeroFrobeniusBalance (data : Input Phi) (X : D) (degree : ℕ+) :
    degree.val •
          (0 : Algebra.GrothendieckAddGroup (Phi.obj X).carrier) +
        Algebra.GrothendieckAddGroup.of 0 =
      gpPullback Phi (𝟙 X) 0 + data.divisor X 0 := by
  simp

/-- A degree-`n` Frobenius endomorphism of a zero-divisor object. -/
def zeroFrobenius (data : Input Phi) (X : D) (degree : ℕ+) :
    zeroObject Phi data X ⟶ zeroObject Phi data X where
  frobeniusDegree := degree
  base := 𝟙 X
  divisor := 0
  rationalFunction := 0
  balance := by
    dsimp [zeroObject]
    exact zeroFrobeniusBalance Phi data X degree

/-- The Frobenius trivialization of the paper's objects `(A_D, 0)`. -/
def zeroFrobeniusTrivialization (data : Input Phi) (X : D) :
    (preFrobenioid Phi data).FrobeniusTrivialization
      (zeroObject Phi data X) where
  lift := zeroFrobenius Phi data X
  map_one := by
    apply Hom.ext <;> rfl
  map_mul m n := by
    apply Hom.ext
    · rfl
    · change 𝟙 X = 𝟙 X ≫ 𝟙 X
      simp
    · simp [zeroFrobenius]
    · simp [zeroFrobenius]
  degree_section _ := rfl
  base_identity _ := by
    change 𝟙 X = 𝟙 X
    rfl
  of_frobenius_type degree := by
    rw [isOfFrobeniusType_iff Phi data]
    constructor
    · rfl
    · change IsIso (𝟙 X)
      infer_instance

theorem zeroObject_isFrobeniusTrivial (data : Input Phi) (X : D) :
    (preFrobenioid Phi data).IsFrobeniusTrivial
      (zeroObject Phi data X) :=
  ⟨zeroFrobeniusTrivialization Phi data X⟩

/-- Definition 1.3(i)(a) for the model category. -/
theorem baseRepresented (data : Input Phi) (B : D) :
    ∃ A : Carrier Phi data,
      (preFrobenioid Phi data).IsFrobeniusTrivial A ∧
        Nonempty (((preFrobenioid Phi data).base).obj A ≅ B) :=
  ⟨zeroObject Phi data B, zeroObject_isFrobeniusTrivial Phi data B,
    ⟨Iso.refl B⟩⟩

/-- The codomain `(A_D, n alpha)` of the canonical degree-`n` arrow. -/
def frobeniusCodomain (data : Input Phi) (object : Carrier Phi data)
    (degree : ℕ+) : Carrier Phi data where
  base := Object.base object
  divisorClass := degree.val • object.divisorClass

/-- The canonical degree-`n` Frobenius-type arrow from a model object. -/
def frobeniusArrow (data : Input Phi) (object : Carrier Phi data)
    (degree : ℕ+) :
    object ⟶ frobeniusCodomain Phi data object degree where
  frobeniusDegree := degree
  base := 𝟙 (Object.base object)
  divisor := 0
  rationalFunction := 0
  balance := by
    dsimp [frobeniusCodomain]
    rw [gpPullback_id]
    simp only [map_zero, add_zero]
    change degree.val • object.divisorClass =
      degree.val • object.divisorClass
    rfl

theorem frobeniusArrow_ofFrobeniusType (data : Input Phi)
    (object : Carrier Phi data) (degree : ℕ+) :
    (preFrobenioid Phi data).IsOfFrobeniusType
      (frobeniusArrow Phi data object degree) := by
  rw [isOfFrobeniusType_iff Phi data]
  constructor
  · rfl
  · change IsIso (𝟙 (Object.base object))
    infer_instance

/--
The comparison from `(A_D, n alpha)` to the codomain of any competing
degree-`n` Frobenius-type arrow.
-/
def frobeniusComparison (data : Input Phi)
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (ofFrobeniusType :
      (preFrobenioid Phi data).IsOfFrobeniusType arrow)
    {degree : ℕ+}
    (degree_eq : (preFrobenioid Phi data).frobeniusDegree arrow = degree) :
    frobeniusCodomain Phi data source degree ⟶ target where
  frobeniusDegree := 1
  base := arrow.base
  divisor := 0
  rationalFunction := arrow.rationalFunction
  balance := by
    rw [isOfFrobeniusType_iff Phi data] at ofFrobeniusType
    change arrow.frobeniusDegree = degree at degree_eq
    have isometric := ofFrobeniusType.1
    change arrow.divisor = 0 at isometric
    dsimp [frobeniusCodomain]
    have arrowBalance := arrow.balance
    rw [degree_eq, isometric] at arrowBalance
    conv_lhs =>
      lhs
      change (1 : ℕ) • (degree.val • source.divisorClass)
    rw [one_nsmul]
    exact arrowBalance

theorem frobeniusComparison_isIso
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (ofFrobeniusType :
      (preFrobenioid Phi data).IsOfFrobeniusType arrow)
    {degree : ℕ+}
    (degree_eq : (preFrobenioid Phi data).frobeniusDegree arrow = degree) :
    IsIso (frobeniusComparison Phi data arrow ofFrobeniusType degree_eq) := by
  apply isIso_of_preStep_isometric Phi data
  · constructor
    · rfl
    · rw [isOfFrobeniusType_iff Phi data] at ofFrobeniusType
      exact ofFrobeniusType.2
  · rfl

theorem frobeniusArrow_comp_comparison
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (ofFrobeniusType :
      (preFrobenioid Phi data).IsOfFrobeniusType arrow)
    {degree : ℕ+}
    (degree_eq : (preFrobenioid Phi data).frobeniusDegree arrow = degree) :
    frobeniusArrow Phi data source degree ≫
        frobeniusComparison Phi data arrow ofFrobeniusType degree_eq =
      arrow := by
  apply Hom.ext
  · change degree * 1 = arrow.frobeniusDegree
    change arrow.frobeniusDegree = degree at degree_eq
    rw [degree_eq]
    exact mul_one degree
  · change 𝟙 (Object.base source) ≫ arrow.base = arrow.base
    simp
  · change
      Phi.pullback (𝟙 (Object.base source)) 0 + 1 • 0 =
        arrow.divisor
    rw [isOfFrobeniusType_iff Phi data] at ofFrobeniusType
    have isometric := ofFrobeniusType.1
    change arrow.divisor = 0 at isometric
    rw [isometric]
    simp
  · change
      data.rationalFunctions.pullback (𝟙 (Object.base source))
          arrow.rationalFunction + 1 • 0 = arrow.rationalFunction
    rw [data.rationalFunctions.pullback_id]
    simp

/-- Definition 1.3(ii), including essential uniqueness, for the model category. -/
def frobeniusDegreeWitness
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    (object : Carrier Phi data) (degree : ℕ+) :
    (preFrobenioid Phi data).FrobeniusDegreeWitness object degree where
  codomain := frobeniusCodomain Phi data object degree
  hom := frobeniusArrow Phi data object degree
  ofFrobeniusType :=
    frobeniusArrow_ofFrobeniusType Phi data object degree
  degree := rfl
  essentiallyUnique := by
    intro target arrow ofFrobeniusType degree_eq
    let comparison :=
      frobeniusComparison Phi data arrow ofFrobeniusType degree_eq
    letI : IsIso comparison :=
      frobeniusComparison_isIso Phi data arrow ofFrobeniusType degree_eq
    refine ⟨asIso comparison, ?_, ?_⟩
    · exact frobeniusArrow_comp_comparison Phi data arrow
        ofFrobeniusType degree_eq
    · intro candidate candidate_comp
      apply Iso.ext
      letI : Epi (frobeniusArrow Phi data object degree) :=
        epi Phi data baseTotallyEpimorphic
          (frobeniusArrow Phi data object degree)
      apply (cancel_epi (frobeniusArrow Phi data object degree)).mp
      exact candidate_comp.trans
        (frobeniusArrow_comp_comparison Phi data arrow
          ofFrobeniusType degree_eq).symm

/--
Since every model object is isotropic, its identity is its isotropic hull.
This proves Definition 1.3(vii)(a) with the full universal property.
-/
def isotropicHull (object : Carrier Phi data) :
    (preFrobenioid Phi data).IsotropicHull object where
  hull := object
  hom := 𝟙 object
  preStep := by
    constructor
    · exact (preFrobenioid Phi data).frobeniusDegree_id object
    · change IsIso (𝟙 (Object.base object))
      infer_instance
  isometric := (preFrobenioid Phi data).divisor_id object
  isotropic := isIsotropic Phi data object
  lift := by
    intro target arrow _
    refine ⟨arrow, by simp, ?_⟩
    intro candidate candidate_comp
    simpa using candidate_comp

/-- Definition 1.3(vii)(b) for model objects. -/
theorem isotropic_closedUnderTargets
    {source target : Carrier Phi data} (_arrow : source ⟶ target)
    (_sourceIsotropic : (preFrobenioid Phi data).IsIsotropic source) :
    (preFrobenioid Phi data).IsIsotropic target :=
  isIsotropic Phi data target

/-- Definition 1.3(iii)(a) for model arrows. -/
theorem coAngular_comp
    {source middle target : Carrier Phi data}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (_firstCoAngular : (preFrobenioid Phi data).IsCoAngular first)
    (_secondCoAngular : (preFrobenioid Phi data).IsCoAngular second) :
    (preFrobenioid Phi data).IsCoAngular (first ≫ second) :=
  isCoAngular Phi data (first ≫ second)

/-- Definition 1.3(iii)(b) for model arrows. -/
theorem parallelToCoAngularPreStep
    {source target : Carrier Phi data} (first second : source ⟶ target)
    (_firstPreStep : (preFrobenioid Phi data).IsPreStep first)
    (_firstCoAngular : (preFrobenioid Phi data).IsCoAngular first) :
    (preFrobenioid Phi data).IsCoAngular second :=
  isCoAngular Phi data second

/--
The model category packaged with the connectedness and total-epimorphicity
hypotheses of Definition 1.1(iv). This does not yet assert the seven axiom
groups of Definition 1.3.
-/
def preFrobenioidPresentation [IsConnected D]
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f) :
    PreFrobenioidPresentation where
  carrier := @Cat.of (Carrier Phi data) (carrierCategory Phi data)
  baseCategory := Cat.of D
  isFSM := IsFSM
  preFrobenioid := preFrobenioid Phi data
  carrierConnected := isConnected Phi data
  baseConnected := (inferInstance : IsConnected D)
  carrierTotallyEpimorphic := epi Phi data baseTotallyEpimorphic
  baseTotallyEpimorphic := baseTotallyEpimorphic

end Carrier

end

end SourceModelFrobenioid

end Iut
