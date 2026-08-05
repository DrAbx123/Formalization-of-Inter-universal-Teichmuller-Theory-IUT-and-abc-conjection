/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidModelType
import Iut.Foundations.SourceModelRationalMonoidTransport

/-!
# The model Frobenioid is of pre-model type

This file constructs the base-Frobenius pair specified in the proof of
Frobenioids I, Theorem 5.2(ii).  Its objects are the zero-divisor objects
`(A_D, 0)`, its arrows have zero divisor and rational-function components, and
its Frobenius section consists of the canonical degree-`n` endomorphisms.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid.Carrier

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- The zero-divisor objects and zero-component arrows form a functor from `D`. -/
def zeroBaseFunctor : D ⥤ Carrier Phi data where
  obj := zeroObject Phi data
  map := zeroBaseArrow Phi data
  map_id X := by
    apply Hom.ext <;> rfl
  map_comp f g := by
    apply Hom.ext
    · rfl
    · rfl
    · simp [zeroBaseArrow]
    · simp [zeroBaseArrow]

/-- A zero-section arrow satisfies the full representable pullback property. -/
theorem zeroBaseArrow_isPullback {X Y : D} (f : X ⟶ Y) :
    (preFrobenioid Phi data).IsPullback (zeroBaseArrow Phi data f) := by
  intro test
  constructor
  · intro left right equality
    have compositeEquality := congrArg
      PreFrobenioid.PullbackComparisonTarget.toCodomain equality
    have baseEquality := congrArg
      PreFrobenioid.PullbackComparisonTarget.toBaseDomain equality
    apply Hom.ext
    · have projected := congrArg Hom.frobeniusDegree compositeEquality
      change left.frobeniusDegree * 1 = right.frobeniusDegree * 1 at projected
      simpa [one_nsmul] using projected
    · exact baseEquality
    · have projected := congrArg Hom.divisor compositeEquality
      change Phi.pullback left.base 0 + 1 • left.divisor =
        Phi.pullback right.base 0 + 1 • right.divisor at projected
      simpa [one_nsmul] using projected
    · have projected := congrArg Hom.rationalFunction compositeEquality
      change data.rationalFunctions.pullback left.base 0 +
          1 • left.rationalFunction =
        data.rationalFunctions.pullback right.base 0 +
          1 • right.rationalFunction at projected
      simpa only [map_zero, zero_add, one_nsmul] using projected
  · intro value
    let baseMap : Object.base test ⟶ X := value.toBaseDomain
    let lift : test ⟶ zeroObject Phi data X :=
      { frobeniusDegree := value.toCodomain.frobeniusDegree
        base := baseMap
        divisor := value.toCodomain.divisor
        rationalFunction := value.toCodomain.rationalFunction
        balance := by
          change value.toCodomain.frobeniusDegree.val • test.divisorClass +
              Algebra.GrothendieckAddGroup.of value.toCodomain.divisor =
            gpPullback Phi baseMap 0 +
              data.divisor (Object.base test) value.toCodomain.rationalFunction
          rw [map_zero, zero_add]
          have balance := value.toCodomain.balance
          change value.toCodomain.frobeniusDegree.val • test.divisorClass +
              Algebra.GrothendieckAddGroup.of value.toCodomain.divisor =
            gpPullback Phi value.toCodomain.base 0 +
              data.divisor (Object.base test) value.toCodomain.rationalFunction
            at balance
          simpa only [map_zero, zero_add] using balance }
    refine ⟨lift, ?_⟩
    cases value with
    | mk toCodomain toBaseDomain commutes =>
      dsimp only [PreFrobenioid.pullbackComparison]
      congr 1
      apply Hom.ext
      · change toCodomain.frobeniusDegree * 1 =
          toCodomain.frobeniusDegree
        simp
      · exact commutes.symm
      · simp [lift, zeroBaseArrow, one_nsmul]
      · simp [lift, zeroBaseArrow, one_nsmul]

/-- The skeletal zero-divisor base-section from the proof of Theorem 5.2(ii). -/
def zeroBaseSection : (preFrobenioid Phi data).BaseSection where
  sectionCategory := Cat.of (Skeleton D)
  inclusion := fromSkeleton D ⋙ zeroBaseFunctor (Phi := Phi) (data := data)
  skeletal := skeleton_skeletal D
  inclusion_faithful := by
    constructor
    intro X Y f g equality
    apply (fromSkeleton D).map_injective
    exact congrArg Hom.base equality
  map_isPullback f :=
    zeroBaseArrow_isPullback (Phi := Phi) (data := data) f.hom
  base_isEquivalence := by
    change (fromSkeleton D ⋙
      (zeroBaseFunctor (Phi := Phi) (data := data) ⋙
        (preFrobenioid Phi data).base)).IsEquivalence
    change (fromSkeleton D ⋙ Functor.id D).IsEquivalence
    infer_instance
  object_frobeniusTrivial X :=
    zeroObject_isFrobeniusTrivial Phi data X.out

/-- The canonical degree-`n` endomorphisms are natural on the zero section. -/
def zeroFrobeniusNaturalTransformation (degree : ℕ+) :
    (zeroBaseSection (Phi := Phi) (data := data)).inclusion ⟶
      (zeroBaseSection (Phi := Phi) (data := data)).inclusion where
  app X := zeroFrobenius Phi data X.out degree
  naturality X Y f := by
    apply Hom.ext
    · change 1 * degree = degree * 1
      simp
    · change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp
    · rw [comp_divisor, comp_divisor]
      dsimp [zeroBaseSection, zeroBaseFunctor, zeroFrobenius, zeroBaseArrow]
      calc
        _ = 0 + 0 := congrArg₂ (fun left right ↦ left + right)
          (map_zero (Phi.pullback f.hom)) (nsmul_zero degree.val)
        _ = _ := (congrArg₂ (fun left right ↦ left + right)
          (map_zero (Phi.pullback (𝟙 X.out))) (nsmul_zero 1)).symm
    · rw [comp_rationalFunction, comp_rationalFunction]
      dsimp [zeroBaseSection, zeroBaseFunctor, zeroFrobenius, zeroBaseArrow]
      calc
        _ = 0 + 0 := congrArg₂ (fun left right ↦ left + right)
          (map_zero (data.rationalFunctions.pullback f.hom))
          (nsmul_zero degree.val)
        _ = _ := (congrArg₂ (fun left right ↦ left + right)
          (map_zero (data.rationalFunctions.pullback (𝟙 X.out)))
          (nsmul_zero 1)).symm

/-- The paper's canonical Frobenius section on the zero base-section. -/
def zeroFrobeniusSection :
    (preFrobenioid Phi data).FrobeniusSection
      (zeroBaseSection (Phi := Phi) (data := data)) where
  lift := zeroFrobeniusNaturalTransformation
  map_one := by
    ext X
    apply Hom.ext <;> rfl
  map_mul m n := by
    ext X
    apply Hom.ext
    · rfl
    · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      simp
    · change 0 = Phi.pullback (𝟙 _) 0 + n.val • 0
      simp
    · change 0 = data.rationalFunctions.pullback (𝟙 _) 0 + n.val • 0
      simp
  degree_section _ _ := rfl
  base_identity _ _ := rfl
  of_frobenius_type degree X :=
    (zeroFrobeniusTrivialization Phi data X.out).of_frobenius_type degree

/-- The explicit base-Frobenius pair of Theorem 5.2(ii). -/
def baseFrobeniusPair : (preFrobenioid Phi data).BaseFrobeniusPair where
  baseSection := zeroBaseSection
  frobeniusSection := zeroFrobeniusSection

/-- The model Frobenioid satisfies the pre-model half of Definition 4.5(i). -/
theorem isPreModelType : (preFrobenioid Phi data).IsPreModelType :=
  ⟨isIsotropic Phi data, ⟨baseFrobeniusPair⟩⟩

end

end Iut.SourceModelFrobenioid.Carrier
