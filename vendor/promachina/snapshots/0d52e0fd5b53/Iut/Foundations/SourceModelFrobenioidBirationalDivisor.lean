/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidBirationalDictionary

/-!
# Birational divisor subfunctor and exact sequence

Frobenioids I, Proposition 4.4(iii) defines `Phi^birat` inside `Phi^gp` and
identifies it as the quotient of target rational functions by the image of
source units. This file constructs the group-valued elementary Frobenioids,
the factorization through `F_(Phi^birat)`, the naturally commutative source
square, and the exact target divisor sequence using actual source
base-identity automorphisms.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- A contravariant subgroup family inside the groupification of `Phi`. -/
@[ext]
structure GroupifiedDivisorSubfunctor where
  obj : ∀ X : D,
    AddSubgroup (Algebra.GrothendieckAddGroup (Phi.obj X).carrier)
  pullback_mem :
    ∀ {X Y : D} (f : X ⟶ Y) {value :
      Algebra.GrothendieckAddGroup (Phi.obj Y).carrier},
      value ∈ obj Y → gpPullback Phi f value ∈ obj X

namespace GroupifiedDivisorSubfunctor

/-- Pullback restricted to a groupified divisor subfunctor. -/
def pullback (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    {X Y : D} (f : X ⟶ Y) : candidate.obj Y →+ candidate.obj X where
  toFun value :=
    ⟨gpPullback Phi f value.1, candidate.pullback_mem f value.property⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (gpPullback Phi f)
  map_add' first second := by
    apply Subtype.ext
    exact map_add (gpPullback Phi f) first.1 second.1

@[simp]
theorem pullback_coe (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    {X Y : D} (f : X ⟶ Y) (value : candidate.obj Y) :
    ((candidate.pullback f value : candidate.obj X) :
        Algebra.GrothendieckAddGroup (Phi.obj X).carrier) =
      gpPullback Phi f value.1 :=
  rfl

theorem pullback_id (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    (X : D) :
    candidate.pullback (𝟙 X) = AddMonoidHom.id (candidate.obj X) := by
  apply AddMonoidHom.ext
  intro value
  apply Subtype.ext
  rw [pullback_coe, gpPullback_id]
  rfl

theorem pullback_comp (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    candidate.pullback (f ≫ g) =
      (candidate.pullback f).comp (candidate.pullback g) := by
  apply AddMonoidHom.ext
  intro value
  apply Subtype.ext
  change gpPullback Phi (f ≫ g) value.1 =
    gpPullback Phi f (gpPullback Phi g value.1)
  rw [gpPullback_comp]
  rfl

/-- The full groupification `Phi^gp`, regarded as a subgroup family. -/
def full (Phi : DivisorialMonoidOn D IsFSM) :
    GroupifiedDivisorSubfunctor (Phi := Phi) where
  obj _ := ⊤
  pullback_mem _ _ membership := membership

end GroupifiedDivisorSubfunctor

/-- An arrow in the elementary Frobenioid attached to a group subfunctor. -/
@[ext]
structure GroupifiedElementaryHom
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi)) (X Y : D) where
  base : X ⟶ Y
  divisor : candidate.obj X
  frobeniusDegree : ℕ+

namespace GroupifiedElementaryHom

/-- Identity in a groupified elementary Frobenioid. -/
def id (candidate : GroupifiedDivisorSubfunctor (Phi := Phi)) (X : D) :
    GroupifiedElementaryHom candidate X X where
  base := 𝟙 X
  divisor := 0
  frobeniusDegree := 1

/-- Composition with the source formula
`Div(g ∘ f) = f^* Div(g) + deg(g) Div(f)`. -/
def comp (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    {X Y Z : D} (first : GroupifiedElementaryHom candidate X Y)
    (second : GroupifiedElementaryHom candidate Y Z) :
    GroupifiedElementaryHom candidate X Z where
  base := first.base ≫ second.base
  divisor := candidate.pullback first.base second.divisor +
    second.frobeniusDegree.val • first.divisor
  frobeniusDegree := first.frobeniusDegree * second.frobeniusDegree

end GroupifiedElementaryHom

/-- An object of the elementary Frobenioid `F_Psi` for a group subfunctor
`Psi ⊆ Phi^gp`. The wrapper separates its category instance from that of `D`. -/
@[ext]
structure GroupifiedElementaryFrobenioid
    (_candidate : GroupifiedDivisorSubfunctor (Phi := Phi)) where
  base : D

namespace GroupifiedElementaryFrobenioid

instance (candidate : GroupifiedDivisorSubfunctor (Phi := Phi)) :
    Category.{u} (GroupifiedElementaryFrobenioid candidate) where
  Hom X Y := GroupifiedElementaryHom candidate X.base Y.base
  id X := GroupifiedElementaryHom.id candidate X.base
  comp first second := GroupifiedElementaryHom.comp candidate first second
  id_comp arrow := by
    ext
    · simp [GroupifiedElementaryHom.comp, GroupifiedElementaryHom.id]
    · change gpPullback Phi (𝟙 _) arrow.divisor.1 +
          arrow.frobeniusDegree.val • 0 = arrow.divisor.1
      rw [gpPullback_id]
      simp
    · simp [GroupifiedElementaryHom.comp, GroupifiedElementaryHom.id]
  comp_id arrow := by
    ext
    · simp [GroupifiedElementaryHom.comp, GroupifiedElementaryHom.id]
    · change gpPullback Phi arrow.base 0 + 1 • arrow.divisor.1 =
        arrow.divisor.1
      rw [map_zero, zero_add, one_nsmul]
    · simp [GroupifiedElementaryHom.comp, GroupifiedElementaryHom.id]
  assoc first second third := by
    ext
    · simp [GroupifiedElementaryHom.comp, Category.assoc]
    · change
        gpPullback Phi (first.base ≫ second.base) third.divisor.1 +
              third.frobeniusDegree.val •
                (gpPullback Phi first.base second.divisor.1 +
                  second.frobeniusDegree.val • first.divisor.1) =
            gpPullback Phi first.base
                (gpPullback Phi second.base third.divisor.1 +
                  third.frobeniusDegree.val • second.divisor.1) +
              (second.frobeniusDegree.val * third.frobeniusDegree.val) •
                first.divisor.1
      rw [gpPullback_comp]
      simp [nsmul_add, mul_nsmul, add_assoc]
    · simp [GroupifiedElementaryHom.comp, mul_assoc]

@[simp]
theorem id_base
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    (X : GroupifiedElementaryFrobenioid candidate) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base :=
  rfl

@[simp]
theorem id_divisor
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    (X : GroupifiedElementaryFrobenioid candidate) :
    (𝟙 X : X ⟶ X).divisor = 0 :=
  rfl

@[simp]
theorem id_frobeniusDegree
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    (X : GroupifiedElementaryFrobenioid candidate) :
    (𝟙 X : X ⟶ X).frobeniusDegree = 1 :=
  rfl

@[simp]
theorem comp_base
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    {X Y Z : GroupifiedElementaryFrobenioid candidate}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    (first ≫ second).base = first.base ≫ second.base :=
  rfl

@[simp]
theorem comp_divisor
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    {X Y Z : GroupifiedElementaryFrobenioid candidate}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    (first ≫ second).divisor =
      candidate.pullback first.base second.divisor +
        second.frobeniusDegree.val • first.divisor :=
  rfl

@[simp]
theorem coe_comp_divisor
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    {X Y Z : GroupifiedElementaryFrobenioid candidate}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    ((first ≫ second).divisor :
        Algebra.GrothendieckAddGroup (Phi.obj X.base).carrier) =
      gpPullback Phi first.base second.divisor.1 +
        second.frobeniusDegree.val • first.divisor.1 :=
  rfl

@[simp]
theorem comp_frobeniusDegree
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    {X Y Z : GroupifiedElementaryFrobenioid candidate}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    (first ≫ second).frobeniusDegree =
      first.frobeniusDegree * second.frobeniusDegree :=
  rfl

/-- Inclusion `F_Psi → F_(Phi^gp)` induced by `Psi ⊆ Phi^gp`. -/
def inclusion
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi)) :
    GroupifiedElementaryFrobenioid candidate ⥤
      GroupifiedElementaryFrobenioid
        (GroupifiedDivisorSubfunctor.full Phi) where
  obj X := ⟨X.base⟩
  map arrow :=
    { base := arrow.base
      divisor := ⟨arrow.divisor.1, trivial⟩
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The elementary inclusion of a divisor subgroup is faithful. -/
theorem inclusion_faithful
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi)) :
    (inclusion candidate).Faithful := by
  constructor
  intro source target first second equality
  apply GroupifiedElementaryHom.ext
  · exact congrArg
      (fun arrow : GroupifiedElementaryHom
          (GroupifiedDivisorSubfunctor.full Phi) source.base target.base ↦
        arrow.base)
      equality
  · apply Subtype.ext
    exact congrArg
      (fun arrow ↦
        ((arrow.divisor :
          (GroupifiedDivisorSubfunctor.full Phi).obj source.base) :
            Algebra.GrothendieckAddGroup (Phi.obj source.base).carrier)) equality
  · exact congrArg
      (fun arrow : GroupifiedElementaryHom
          (GroupifiedDivisorSubfunctor.full Phi) source.base target.base ↦
        arrow.frobeniusDegree) equality

end GroupifiedElementaryFrobenioid

namespace Input

/-- Proposition 4.4(iii)'s `Phi^birat`, objectwise the image of `DivB`. -/
def birationalDivisorSubfunctor (data : Input Phi) :
    GroupifiedDivisorSubfunctor (Phi := Phi) where
  obj := data.birationalDivisors
  pullback_mem := data.gpPullback_mem_birationalDivisors

end Input

namespace BirationalObject

/-- The lower functor `C^birat → F_(Phi^birat)` of Proposition 4.4(iii).
Its divisor coordinate is `DivB(u)`, not the object-class-corrected divisor
used by the naturally isomorphic upper route. -/
def birationalDivisorFunctor :
    BirationalObject (Phi := Phi) (data := data) ⥤
      GroupifiedElementaryFrobenioid
        (Input.birationalDivisorSubfunctor data) where
  obj object := ⟨Object.base object.underlying⟩
  map {X _Y} arrow :=
    { base := arrow.base
      divisor :=
        ⟨data.divisor (Object.base X.underlying)
            arrow.rationalFunction,
          ⟨arrow.rationalFunction, rfl⟩⟩
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := by
    apply GroupifiedElementaryHom.ext
    · rfl
    · apply Subtype.ext
      exact map_zero _
    · rfl
  map_comp {X Y _Z} first second := by
    apply GroupifiedElementaryHom.ext
    · rfl
    · apply Subtype.ext
      change data.divisor (Object.base X.underlying)
          (data.rationalFunctions.pullback first.base
              second.rationalFunction +
            second.frobeniusDegree.val • first.rationalFunction) =
        gpPullback Phi first.base
            (data.divisor (Object.base Y.underlying)
              second.rationalFunction) +
          second.frobeniusDegree.val •
            data.divisor (Object.base X.underlying)
              first.rationalFunction
      rw [map_add, map_nsmul, data.divisor_natural]
    · rfl

/-- The direct lower functor to the full groupification `F_(Phi^gp)`. -/
def groupifiedDivisorFunctor :
    BirationalObject (Phi := Phi) (data := data) ⥤
      GroupifiedElementaryFrobenioid
        (GroupifiedDivisorSubfunctor.full Phi) :=
  birationalDivisorFunctor ⋙
    GroupifiedElementaryFrobenioid.inclusion
      (Input.birationalDivisorSubfunctor data)

/-- Proposition 4.4(iii)'s literal factorization through
`F_(Phi^birat) ⊆ F_(Phi^gp)`. -/
theorem groupifiedDivisorFunctor_factorization :
    groupifiedDivisorFunctor (Phi := Phi) (data := data) =
      birationalDivisorFunctor ⋙
        GroupifiedElementaryFrobenioid.inclusion
          (Input.birationalDivisorSubfunctor data) :=
  rfl

end BirationalObject

namespace Carrier

/-- The upper route `C → F_Phi → F_(Phi^gp)` in Proposition 4.4(i). -/
def groupifiedStructureFunctor :
    Carrier Phi data ⥤
      GroupifiedElementaryFrobenioid
        (GroupifiedDivisorSubfunctor.full Phi) where
  obj object := ⟨Object.base object⟩
  map arrow :=
    { base := arrow.base
      divisor :=
        ⟨Algebra.GrothendieckAddGroup.of arrow.divisor, trivial⟩
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := by
    apply GroupifiedElementaryHom.ext
    · rfl
    · apply Subtype.ext
      exact map_zero _
    · rfl
  map_comp first second := by
    apply GroupifiedElementaryHom.ext
    · rfl
    · apply Subtype.ext
      change Algebra.GrothendieckAddGroup.of
          (Phi.pullback first.base second.divisor +
            second.frobeniusDegree.val • first.divisor) =
        gpPullback Phi first.base
            (Algebra.GrothendieckAddGroup.of second.divisor) +
          second.frobeniusDegree.val •
            Algebra.GrothendieckAddGroup.of first.divisor
      rw [map_add, map_nsmul, gpPullback_of]
    · rfl

/-- The component correcting the upper divisor `Div(phi)` to the lower
divisor `DivB(u_phi)`. Its divisor is the negative object class. -/
def groupifiedStructureComparisonApp (object : Carrier Phi data) :
    (groupifiedStructureFunctor (Phi := Phi) (data := data)).obj object ≅
      ((BirationalObject.inclusionFunctor (Phi := Phi) (data := data)) ⋙
        BirationalObject.groupifiedDivisorFunctor).obj object where
  hom :=
    { base := 𝟙 (Object.base object)
      divisor := ⟨-object.divisorClass, trivial⟩
      frobeniusDegree := 1 }
  inv :=
    { base := 𝟙 (Object.base object)
      divisor := ⟨object.divisorClass, trivial⟩
      frobeniusDegree := 1 }
  hom_inv_id := by
    apply GroupifiedElementaryHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp
    · apply Subtype.ext
      simp only [Functor.comp_obj,
        GroupifiedElementaryFrobenioid.comp_divisor, PNat.val_ofNat,
        AddSubgroup.coe_add, GroupifiedDivisorSubfunctor.pullback_coe,
        AddSubmonoidClass.coe_nsmul,
        GroupifiedElementaryFrobenioid.id_divisor, ZeroMemClass.coe_zero]
      have pullbackIdentity :
          gpPullback Phi (𝟙 (Object.base object)) object.divisorClass =
            object.divisorClass := by
        exact DFunLike.congr_fun (gpPullback_id Phi (Object.base object))
          object.divisorClass
      calc
        gpPullback Phi (𝟙 (Object.base object)) object.divisorClass +
              1 • (-object.divisorClass) =
            object.divisorClass + 1 • (-object.divisorClass) :=
          congrArg (fun value ↦ value + 1 • (-object.divisorClass))
            pullbackIdentity
        _ = 0 := by
          rw [one_nsmul]
          exact add_neg_cancel object.divisorClass
    · change (1 : ℕ+) * 1 = 1
      simp
  inv_hom_id := by
    apply GroupifiedElementaryHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp
    · apply Subtype.ext
      simp only [Functor.comp_obj,
        GroupifiedElementaryFrobenioid.comp_divisor, PNat.val_ofNat,
        AddSubgroup.coe_add, GroupifiedDivisorSubfunctor.pullback_coe,
        AddSubmonoidClass.coe_nsmul,
        GroupifiedElementaryFrobenioid.id_divisor, ZeroMemClass.coe_zero]
      have pullbackIdentity :
          gpPullback Phi (𝟙 (Object.base object)) (-object.divisorClass) =
            -object.divisorClass := by
        exact DFunLike.congr_fun (gpPullback_id Phi (Object.base object))
          (-object.divisorClass)
      calc
        gpPullback Phi (𝟙 (Object.base object)) (-object.divisorClass) +
              1 • object.divisorClass =
            -object.divisorClass + 1 • object.divisorClass :=
          congrArg (fun value ↦ value + 1 • object.divisorClass)
            pullbackIdentity
        _ = 0 := by
          rw [one_nsmul]
          exact neg_add_cancel object.divisorClass
    · change (1 : ℕ+) * 1 = 1
      simp

/-- Proposition 4.4(i)'s 1-commutativity for the model: the original
groupified zero-divisor functor is naturally isomorphic to localization
followed by the `DivB` functor. -/
def groupifiedStructureComparison :
    groupifiedStructureFunctor (Phi := Phi) (data := data) ≅
      BirationalObject.inclusionFunctor ⋙
        BirationalObject.groupifiedDivisorFunctor :=
  NatIso.ofComponents groupifiedStructureComparisonApp (fun {X Y} arrow ↦ by
    apply GroupifiedElementaryHom.ext
    · change arrow.base ≫ 𝟙 _ = 𝟙 _ ≫ arrow.base
      simp
    · apply Subtype.ext
      rw [GroupifiedElementaryFrobenioid.coe_comp_divisor,
        GroupifiedElementaryFrobenioid.coe_comp_divisor]
      dsimp [groupifiedStructureFunctor, groupifiedStructureComparisonApp,
        BirationalObject.groupifiedDivisorFunctor,
        BirationalObject.birationalDivisorFunctor,
        BirationalObject.inclusionFunctor,
        GroupifiedElementaryFrobenioid.inclusion,
        GroupifiedElementaryHom.comp]
      have pullbackNeg :
          gpPullback Phi arrow.base (-Y.divisorClass) =
            -(gpPullback Phi arrow.base Y.divisorClass) :=
        map_neg (gpPullback Phi arrow.base) Y.divisorClass
      have pullbackIdentity :
          gpPullback Phi (𝟙 (Object.base X))
              (data.divisor (Object.base X) arrow.rationalFunction) =
            data.divisor (Object.base X) arrow.rationalFunction := by
        exact DFunLike.congr_fun (gpPullback_id Phi (Object.base X))
          (data.divisor (Object.base X) arrow.rationalFunction)
      have balance := arrow.balance
      have divisorBalance :
          Algebra.GrothendieckAddGroup.of arrow.divisor =
            gpPullback Phi arrow.base Y.divisorClass +
              data.divisor (Object.base X) arrow.rationalFunction -
              arrow.frobeniusDegree.val • X.divisorClass := by
        calc
          _ = (arrow.frobeniusDegree.val • X.divisorClass +
                  Algebra.GrothendieckAddGroup.of arrow.divisor) -
                arrow.frobeniusDegree.val • X.divisorClass := by
            abel
          _ = (gpPullback Phi arrow.base Y.divisorClass +
                  data.divisor (Object.base X) arrow.rationalFunction) -
                arrow.frobeniusDegree.val • X.divisorClass :=
            congrArg
              (fun value ↦
                value - arrow.frobeniusDegree.val • X.divisorClass)
              balance
      have nsmulNegative :
          arrow.frobeniusDegree.val • (-X.divisorClass) =
            -(arrow.frobeniusDegree.val • X.divisorClass) := by
        induction arrow.frobeniusDegree.val with
        | zero => simp
        | succ degree inductionHypothesis =>
            rw [succ_nsmul, succ_nsmul, inductionHypothesis]
            abel
      calc
        gpPullback Phi arrow.base (-Y.divisorClass) +
              1 • Algebra.GrothendieckAddGroup.of arrow.divisor =
            -(gpPullback Phi arrow.base Y.divisorClass) +
              Algebra.GrothendieckAddGroup.of arrow.divisor := by
          rw [pullbackNeg, one_nsmul]
        _ = data.divisor (Object.base X) arrow.rationalFunction +
              arrow.frobeniusDegree.val • (-X.divisorClass) := by
          rw [divisorBalance]
          rw [nsmulNegative]
          abel
        _ = gpPullback Phi (𝟙 (Object.base X))
                (data.divisor (Object.base X) arrow.rationalFunction) +
              arrow.frobeniusDegree.val • (-X.divisorClass) := by
          rw [pullbackIdentity]
    · change arrow.frobeniusDegree * 1 =
        1 * arrow.frobeniusDegree
      simp)

end Carrier

namespace Carrier.ColimitBirationalObject

/-- Proposition 4.4(iii)'s divisor functor on the Hom-colimit
birationalization. -/
def birationalDivisorFunctor :
    ColimitBirationalObject (Phi := Phi) (data := data) ⥤
      GroupifiedElementaryFrobenioid
        (Input.birationalDivisorSubfunctor data) :=
  comparisonFunctor (Phi := Phi) (data := data) ⋙
    BirationalObject.birationalDivisorFunctor

/-- The colimit divisor functor followed by the subgroup inclusion. -/
def groupifiedDivisorFunctor :
    ColimitBirationalObject (Phi := Phi) (data := data) ⥤
      GroupifiedElementaryFrobenioid
        (GroupifiedDivisorSubfunctor.full Phi) :=
  comparisonFunctor (Phi := Phi) (data := data) ⋙
    BirationalObject.groupifiedDivisorFunctor

/-- The actual colimit functor factors through `F_(Phi^birat)`. -/
theorem groupifiedDivisorFunctor_factorization :
    groupifiedDivisorFunctor (Phi := Phi) (data := data) =
      birationalDivisorFunctor ⋙
        GroupifiedElementaryFrobenioid.inclusion
          (Input.birationalDivisorSubfunctor data) :=
  rfl

/-- The divisor map corestricted to its birational image. -/
def birationalDivisorRangeHom (data : Input Phi) (X : D) :
    Multiplicative (data.rationalFunctions.obj X) →*
      Multiplicative (data.birationalDivisors X) :=
  (data.divisor X).rangeRestrict.toMultiplicative

/-- The target rational-function divisor homomorphism of Proposition 4.4(iii). -/
def birationalDivisorHom
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object →*
      Multiplicative
        (data.birationalDivisors (Object.base object.underlying)) :=
  (birationalDivisorRangeHom data (Object.base object.underlying)).comp
    (rationalFunctionEquiv object).toMonoidHom

/-- The birational divisor homomorphism is objectwise surjective. -/
theorem birationalDivisorHom_surjective
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    Function.Surjective (birationalDivisorHom object) := by
  intro value
  rcases value.toAdd.property with ⟨rationalFunction, equality⟩
  let endomorphism :=
    (rationalFunctionEquiv (Phi := Phi) (data := data) object).symm
      (Multiplicative.ofAdd rationalFunction)
  refine ⟨endomorphism, ?_⟩
  apply Multiplicative.ext
  change
    (birationalDivisorRangeHom data (Object.base object.underlying)
      (rationalFunctionEquiv (Phi := Phi) (data := data) object
        endomorphism)).toAdd = value.toAdd
  rw [show rationalFunctionEquiv (Phi := Phi) (data := data) object
      endomorphism = Multiplicative.ofAdd rationalFunction by
    exact (rationalFunctionEquiv (Phi := Phi) (data := data) object).apply_symm_apply
      (Multiplicative.ofAdd rationalFunction)]
  apply Subtype.ext
  exact equality

/-- The target divisor homomorphism is the constructed groupified divisor. -/
theorem birationalDivisorHom_underlying
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (endomorphism :
      (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object) :
    ((birationalDivisorHom object endomorphism).toAdd :
        data.birationalDivisors (Object.base object.underlying)).1 =
      groupifiedDivisorClass endomorphism.hom := by
  let value :=
    rationalFunctionEquiv (Phi := Phi) (data := data) object endomorphism
  have endomorphismEquality :
      rationalFunctionEndomorphism (Phi := Phi) (data := data) object value =
        endomorphism :=
    (rationalFunctionEquiv (Phi := Phi) (data := data) object).symm_apply_apply
      endomorphism
  change data.divisor (Object.base object.underlying) value.toAdd =
    groupifiedDivisorClass endomorphism.hom
  rw [← endomorphismEquality]
  exact (rationalFunctionEndomorphism_groupifiedDivisorClass
    object value).symm

/-- A source unit has rational function in the kernel of `DivB`. -/
theorem sourceUnit_rationalFunction_divisor_eq_zero
    (object : Carrier Phi data)
    (unit : (Carrier.preFrobenioid Phi data).BaseIdentityAutomorphism object) :
    data.divisor (Object.base object) unit.iso.hom.rationalFunction = 0 := by
  letI : IsIso unit.iso.hom := unit.iso.isIso_hom
  have linearIsometric := Carrier.isIso_linear_isometric
    (Phi := Phi) (data := data) unit.iso.hom
  let endomorphism :
      (Carrier.preFrobenioid Phi data).LinearBaseIdentityEndomorphism object :=
    { hom := unit.iso.hom
      linear := linearIsometric.1
      baseIdentity := unit.baseIdentity }
  have divisorFormula := Carrier.endomorphism_divisor_eq
    (Phi := Phi) (data := data) endomorphism
  have isometric := linearIsometric.2
  change unit.iso.hom.divisor = 0 at isometric
  rw [isometric] at divisorFormula
  simpa using divisorFormula.symm

/-- A kernel rational function produces an actual source unit. -/
def sourceUnitOfDivisorEqZero
    (object : Carrier Phi data)
    (rationalFunction : data.rationalFunctions.obj (Object.base object))
    (divisorEq : data.divisor (Object.base object) rationalFunction = 0) :
    (Carrier.preFrobenioid Phi data).BaseIdentityAutomorphism object := by
  let hom : object ⟶ object :=
    { frobeniusDegree := 1
      base := 𝟙 (Object.base object)
      divisor := 0
      rationalFunction := rationalFunction
      balance := by
        change (1 : ℕ) • object.divisorClass +
              Algebra.GrothendieckAddGroup.of 0 =
            gpPullback Phi (𝟙 (Object.base object)) object.divisorClass +
              data.divisor (Object.base object) rationalFunction
        rw [one_nsmul, gpPullback_id, divisorEq]
        simp }
  have preStep : (Carrier.preFrobenioid Phi data).IsPreStep hom := by
    constructor
    · rfl
    · change IsIso (𝟙 (Object.base object))
      infer_instance
  have isometric : (Carrier.preFrobenioid Phi data).IsIsometric hom := rfl
  letI : IsIso hom := Carrier.isIso_of_preStep_isometric
    (Phi := Phi) (data := data) hom preStep isometric
  exact
    { iso := asIso hom
      baseIdentity := rfl }

@[simp]
theorem sourceUnitOfDivisorEqZero_rationalFunction
    (object : Carrier Phi data)
    (rationalFunction : data.rationalFunctions.obj (Object.base object))
    (divisorEq : data.divisor (Object.base object) rationalFunction = 0) :
    (sourceUnitOfDivisorEqZero object rationalFunction
      divisorEq).iso.hom.rationalFunction = rationalFunction :=
  rfl

/-- The canonical localization sends a source unit to a target endomorphism. -/
def localizationUnitEndomorphism
    (object : Carrier Phi data)
    (unit : (Carrier.preFrobenioid Phi data).BaseIdentityAutomorphism object) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
      ((localizationFunctor (Phi := Phi) (data := data)).obj object) := by
  letI : IsIso unit.iso.hom := unit.iso.isIso_hom
  have linear := (Carrier.isIso_linear_isometric
    (Phi := Phi) (data := data) unit.iso.hom).1
  exact
    { hom := (localizationFunctor (Phi := Phi) (data := data)).map unit.iso.hom
      linear := by
        change ((comparisonFunctor (Phi := Phi) (data := data)).map
          ((localizationFunctor (Phi := Phi) (data := data)).map
            unit.iso.hom)).frobeniusDegree = 1
        rw [comparisonFunctor_map_localizationFunctor]
        exact linear
      baseIdentity := by
        change ((comparisonFunctor (Phi := Phi) (data := data)).map
          ((localizationFunctor (Phi := Phi) (data := data)).map
            unit.iso.hom)).base = 𝟙 _
        rw [comparisonFunctor_map_localizationFunctor]
        exact unit.baseIdentity }

/-- Localization preserves the source unit's rational-function coordinate. -/
theorem rationalFunctionEquiv_localizationUnitEndomorphism
    (object : Carrier Phi data)
    (unit : (Carrier.preFrobenioid Phi data).BaseIdentityAutomorphism object) :
    rationalFunctionEquiv (Phi := Phi) (data := data)
        ((localizationFunctor (Phi := Phi) (data := data)).obj object)
        (localizationUnitEndomorphism object unit) =
      Multiplicative.ofAdd unit.iso.hom.rationalFunction := by
  change Multiplicative.ofAdd
      (((comparisonFunctor (Phi := Phi) (data := data)).map
        ((localizationFunctor (Phi := Phi) (data := data)).map
          unit.iso.hom)).rationalFunction) = _
  rw [comparisonFunctor_map_localizationFunctor]
  rfl

/-- The same compatibility, stated for an arbitrary bundled colimit object. -/
theorem rationalFunctionEquiv_localizationUnitEndomorphism_underlying
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (unit : (Carrier.preFrobenioid Phi data).BaseIdentityAutomorphism
      object.underlying) :
    rationalFunctionEquiv (Phi := Phi) (data := data) object
        (localizationUnitEndomorphism object.underlying unit) =
      Multiplicative.ofAdd unit.iso.hom.rationalFunction :=
  rationalFunctionEquiv_localizationUnitEndomorphism object.underlying unit

/-- The image of actual source units inside target rational functions. -/
def IsInSourceUnitImage
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (endomorphism :
      (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object) : Prop :=
  ∃ unit :
      (Carrier.preFrobenioid Phi data).BaseIdentityAutomorphism
        object.underlying,
    localizationUnitEndomorphism object.underlying unit = endomorphism

/-- Proposition 4.4(iii): the divisor kernel is exactly the source-unit image. -/
theorem birationalDivisorHom_eq_one_iff_sourceUnitImage
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (endomorphism :
      (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object) :
    birationalDivisorHom object endomorphism = 1 ↔
      IsInSourceUnitImage object endomorphism := by
  let value :=
    (rationalFunctionEquiv (Phi := Phi) (data := data) object
      endomorphism).toAdd
  constructor
  · intro kernel
    have divisorEq :
        data.divisor (Object.base object.underlying) value = 0 := by
      have underlying := congrArg
        (fun result : Multiplicative
            (data.birationalDivisors (Object.base object.underlying)) ↦
          ((result.toAdd : data.birationalDivisors
            (Object.base object.underlying)) :
              Algebra.GrothendieckAddGroup
                (Phi.obj (Object.base object.underlying)).carrier)) kernel
      exact underlying
    let unit := sourceUnitOfDivisorEqZero object.underlying value divisorEq
    refine ⟨unit, ?_⟩
    apply (rationalFunctionEquiv (Phi := Phi) (data := data) object).injective
    rw [rationalFunctionEquiv_localizationUnitEndomorphism_underlying]
    exact congrArg Multiplicative.ofAdd
      (sourceUnitOfDivisorEqZero_rationalFunction
        object.underlying value divisorEq).symm
  · rintro ⟨unit, endomorphismEquality⟩
    have equality := congrArg
      (fun targetEndomorphism ↦
        (rationalFunctionEquiv (Phi := Phi) (data := data) object
          targetEndomorphism).toAdd) endomorphismEquality
    change (rationalFunctionEquiv (Phi := Phi) (data := data) object
        (localizationUnitEndomorphism object.underlying unit)).toAdd =
      (rationalFunctionEquiv (Phi := Phi) (data := data) object
        endomorphism).toAdd at equality
    rw [rationalFunctionEquiv_localizationUnitEndomorphism_underlying] at equality
    apply Multiplicative.ext
    apply Subtype.ext
    change data.divisor (Object.base object.underlying)
      ((rationalFunctionEquiv (Phi := Phi) (data := data) object
        endomorphism).toAdd) = 0
    rw [← equality]
    simpa using sourceUnit_rationalFunction_divisor_eq_zero
      object.underlying unit

/-- The factorization and surjectivity properties that characterize `Phi^birat`. -/
structure IsBirationalDivisorFactorization
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi)) : Prop where
  functor_factorization :
    ∀ {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
      (arrow : source ⟶ target),
      (((birationalDivisorFunctor (Phi := Phi) (data := data)).map
          arrow).divisor : data.birationalDivisors
            (Object.base source.underlying)).1 ∈
        candidate.obj (Object.base source.underlying)
  divisor_mem :
    ∀ (object : ColimitBirationalObject (Phi := Phi) (data := data))
      (endomorphism :
        (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
          object),
      groupifiedDivisorClass endomorphism.hom ∈
        candidate.obj (Object.base object.underlying)
  divisor_surjective :
    ∀ (X : D) (value :
      Algebra.GrothendieckAddGroup (Phi.obj X).carrier),
      value ∈ candidate.obj X →
        ∃ endomorphism :
          (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
              (⟨Carrier.zeroObject Phi data X⟩ :
                ColimitBirationalObject (Phi := Phi) (data := data)),
          groupifiedDivisorClass endomorphism.hom = value

/-- The constructed subgroup family has the required factorization property. -/
theorem birationalDivisorSubfunctor_factorization :
    IsBirationalDivisorFactorization (data := data)
      (Input.birationalDivisorSubfunctor data) := by
  constructor
  · intro source target arrow
    exact ((birationalDivisorFunctor (Phi := Phi) (data := data)).map
      arrow).divisor.property
  · intro object endomorphism
    have membership := (birationalDivisorHom object endomorphism).toAdd.property
    rw [birationalDivisorHom_underlying] at membership
    exact membership
  · intro X value membership
    rcases membership with ⟨rationalFunction, equality⟩
    let object : ColimitBirationalObject (Phi := Phi) (data := data) :=
      ⟨Carrier.zeroObject Phi data X⟩
    let endomorphism := rationalFunctionEndomorphism
      (Phi := Phi) (data := data) object
        (Multiplicative.ofAdd rationalFunction)
    refine ⟨endomorphism, ?_⟩
    exact (rationalFunctionEndomorphism_groupifiedDivisorClass
      object (Multiplicative.ofAdd rationalFunction)).trans equality

/-- Any factorizing, objectwise-surjective candidate has the same subgroups. -/
theorem birationalDivisorSubfunctor_unique_objectwise
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    (factorization : IsBirationalDivisorFactorization (data := data) candidate)
    (X : D) :
    candidate.obj X = data.birationalDivisors X := by
  apply le_antisymm
  · intro value membership
    obtain ⟨endomorphism, equality⟩ :=
      factorization.divisor_surjective X value membership
    rw [← equality]
    exact birationalDivisorSubfunctor_factorization.divisor_mem _ endomorphism
  · intro value membership
    rcases membership with ⟨rationalFunction, rfl⟩
    let object : ColimitBirationalObject (Phi := Phi) (data := data) :=
      ⟨Carrier.zeroObject Phi data X⟩
    let endomorphism := rationalFunctionEndomorphism
      (Phi := Phi) (data := data) object
        (Multiplicative.ofAdd rationalFunction)
    have targetMembership := factorization.divisor_mem object endomorphism
    rw [rationalFunctionEndomorphism_groupifiedDivisorClass] at targetMembership
    exact targetMembership

/-- Proposition 4.4(iii)'s uniqueness of the birational divisor subfunctor. -/
theorem birationalDivisorSubfunctor_unique
    (candidate : GroupifiedDivisorSubfunctor (Phi := Phi))
    (factorization : IsBirationalDivisorFactorization (data := data) candidate) :
    candidate = Input.birationalDivisorSubfunctor data := by
  apply GroupifiedDivisorSubfunctor.ext
  funext X
  exact birationalDivisorSubfunctor_unique_objectwise candidate factorization X

end Carrier.ColimitBirationalObject

end

end Iut.SourceModelFrobenioid
