/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidFilteredBirational

/-!
# Pre-Frobenioid structure on the model Hom-colimit birationalization

Frobenioids I, Proposition 4.4(ii) equips the category constructed from the
Hom colimits of Proposition 4.4(i) with a pre-Frobenioid structure over the
zero divisor monoid.  This file constructs that structure on the model, proves
that it is of group-like and Frobenius-normalized type, and proves Definition
4.5(i) model type for the canonical colimit localization functor.

The seven Definition 1.3 axiom groups and the resulting full presentation are
constructed in `SourceModelFrobenioidColimitAxioms`.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

namespace Carrier.ColimitBirationalObject

open CoAngularPreStepOver

/-- The colimit category's functor to the elementary Frobenioid over `0_D`. -/
def structureFunctor :
    ColimitBirationalObject (Phi := Phi) (data := data) ⥤
      ElementaryFrobenioid D IsFSM zeroDivisorialMonoidOn :=
  comparisonFunctor (Phi := Phi) (data := data) ⋙
    BirationalObject.structureFunctor (Phi := Phi) (data := data)

/-- Proposition 4.4(ii)'s pre-Frobenioid structure on the Hom-colimit model. -/
def preFrobenioid :
    PreFrobenioid
      (ColimitBirationalObject (Phi := Phi) (data := data)) D IsFSM where
  divisorMonoid := zeroDivisorialMonoidOn
  structureFunctor := structureFunctor

@[simp]
theorem preFrobenioid_frobeniusDegree
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree arrow =
      (colimitComparisonEquiv source.underlying target.underlying arrow).frobeniusDegree :=
  rfl

@[simp]
theorem preFrobenioid_base_map
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).base.map arrow =
      (colimitComparisonEquiv source.underlying target.underlying arrow).base :=
  rfl

/-- Fully faithful comparison transports linear base-identity endomorphisms. -/
def linearBaseIdentityEndomorphismMap
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object →*
      (BirationalObject.preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        ((comparisonFunctor (Phi := Phi) (data := data)).obj object) where
  toFun alpha :=
    { hom := (comparisonFunctor (Phi := Phi) (data := data)).map alpha.hom
      linear := alpha.linear
      baseIdentity := alpha.baseIdentity }
  map_one' := by
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    exact (comparisonFunctor (Phi := Phi) (data := data)).map_id object
  map_mul' first second := by
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    exact (comparisonFunctor (Phi := Phi) (data := data)).map_comp
      first.hom second.hom

/-- The comparison is bijective on linear base-identity endomorphisms. -/
theorem linearBaseIdentityEndomorphismMap_bijective
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    Function.Bijective
      (linearBaseIdentityEndomorphismMap (Phi := Phi) (data := data)
        object) := by
  constructor
  · intro first second equality
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    apply (comparisonFunctor (Phi := Phi) (data := data)).map_injective
    exact congrArg PreFrobenioid.LinearBaseIdentityEndomorphism.hom equality
  · intro target
    let comparison := comparisonFunctor (Phi := Phi) (data := data)
    let fullyFaithful :=
      comparisonFunctor_fullyFaithful (Phi := Phi) (data := data)
    let sourceHom := fullyFaithful.preimage target.hom
    have mappedSource : comparison.map sourceHom = target.hom :=
      fullyFaithful.map_preimage target.hom
    let source :
        (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
          object :=
      { hom := sourceHom
        linear := by
          change (comparison.map sourceHom).frobeniusDegree = 1
          rw [mappedSource]
          exact target.linear
        baseIdentity := by
          change (comparison.map sourceHom).base = 𝟙 _
          rw [mappedSource]
          exact target.baseIdentity }
    refine ⟨source, ?_⟩
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    exact mappedSource

/-- Comparison equivalence on the endomorphism monoids `O^bullet`. -/
def linearBaseIdentityEndomorphismEquiv
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object ≃*
      (BirationalObject.preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        ((comparisonFunctor (Phi := Phi) (data := data)).obj object) :=
  MulEquiv.ofBijective
    (linearBaseIdentityEndomorphismMap (Phi := Phi) (data := data) object)
    (linearBaseIdentityEndomorphismMap_bijective
      (Phi := Phi) (data := data) object)

/-- Theorem 5.2(ii)'s objectwise rational-function equivalence on the colimit. -/
def rationalFunctionEquiv
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object ≃*
      Multiplicative
        (data.rationalFunctions.obj (Object.base object.underlying)) :=
  (linearBaseIdentityEndomorphismEquiv (Phi := Phi) (data := data) object).trans
    (BirationalObject.rationalFunctionEquiv
      ((comparisonFunctor (Phi := Phi) (data := data)).obj object))

/-- The colimit endomorphism corresponding to a rational function. -/
def rationalFunctionEndomorphism
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (value : Multiplicative
      (data.rationalFunctions.obj (Object.base object.underlying))) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
      object :=
  (rationalFunctionEquiv (Phi := Phi) (data := data) object).symm value

/-- In the group-like target every linear base-identity endomorphism is a unit. -/
theorem linearBaseIdentityEndomorphism_isIso
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (endomorphism :
      (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object) :
    IsIso endomorphism.hom := by
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  have linear : (comparison.map endomorphism.hom).frobeniusDegree = 1 :=
    endomorphism.linear
  have baseIdentity : (comparison.map endomorphism.hom).base = 𝟙 _ :=
    endomorphism.baseIdentity
  have baseIsIso : IsIso (comparison.map endomorphism.hom).base := by
    rw [baseIdentity]
    infer_instance
  haveI : IsIso (comparison.map endomorphism.hom) :=
    (BirationalObject.isoOfLinearBaseIso
      (comparison.map endomorphism.hom) linear baseIsIso).isIso_hom
  exact isIso_of_reflects_iso endomorphism.hom comparison

/-- Proposition 4.4(i)'s groupified divisor on a colimit arrow. -/
def groupifiedDivisorClass
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    Algebra.GrothendieckAddGroup
      (Phi.obj (Object.base source.underlying)).carrier :=
  ((comparisonFunctor (Phi := Phi) (data := data)).map arrow).divisorClass

/-- Under the colimit rational-function equivalence, the divisor is `DivB`. -/
theorem rationalFunctionEndomorphism_groupifiedDivisorClass
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (value : Multiplicative
      (data.rationalFunctions.obj (Object.base object.underlying))) :
    groupifiedDivisorClass
        (rationalFunctionEndomorphism (Phi := Phi) (data := data)
          object value).hom =
      data.divisor (Object.base object.underlying) value.toAdd := by
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  let concreteObject := comparison.obj object
  let sourceEquiv :=
    linearBaseIdentityEndomorphismEquiv (Phi := Phi) (data := data) object
  let targetEquiv := BirationalObject.rationalFunctionEquiv concreteObject
  let sourceEndomorphism :=
    rationalFunctionEndomorphism (Phi := Phi) (data := data) object value
  have mappedEndomorphism : sourceEquiv sourceEndomorphism =
      BirationalObject.rationalFunctionEndomorphism concreteObject value := by
    apply targetEquiv.injective
    change rationalFunctionEquiv (Phi := Phi) (data := data) object
        sourceEndomorphism = value
    exact Equiv.apply_symm_apply _ _
  have mappedHom := congrArg (fun endomorphism ↦ endomorphism.hom)
    mappedEndomorphism
  change comparison.map sourceEndomorphism.hom =
      (BirationalObject.rationalFunctionEndomorphism concreteObject value).hom
    at mappedHom
  dsimp [groupifiedDivisorClass]
  rw [mappedHom]
  exact BirationalObject.rationalFunctionEndomorphism_divisorClass
    concreteObject value

/-- Frobenius normalization transfers from the concrete equivalent target. -/
theorem isFrobeniusNormalized
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).IsFrobeniusNormalized
      object := by
  intro phi phiBase alpha
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  let endomorphismMap :=
    linearBaseIdentityEndomorphismMap (Phi := Phi) (data := data) object
  apply comparison.map_injective
  rw [comparison.map_comp, comparison.map_comp]
  have mappedPower := congrArg (fun endomorphism ↦ endomorphism.hom)
    (map_pow endomorphismMap alpha
      ((preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree phi).val)
  change comparison.map
        (alpha ^
          ((preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree phi).val).hom =
      (endomorphismMap alpha ^
        ((preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree phi).val).hom
    at mappedPower
  rw [mappedPower]
  exact BirationalObject.isFrobeniusNormalized (comparison.obj object)
    (comparison.map phi) phiBase (endomorphismMap alpha)

/-- The colimit birational pre-Frobenioid is Frobenius-normalized. -/
theorem isFrobeniusNormalizedType :
    (preFrobenioid (Phi := Phi) (data := data)).IsFrobeniusNormalizedType :=
  isFrobeniusNormalized

/-- Every object is group-like because the divisor monoid is `0_D`. -/
theorem isGroupLike
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).IsGroupLike object := by
  change ∀ value : PUnit, value = 0
  intro value
  cases value
  rfl

/-- Proposition 4.4(ii)'s group-like-type conclusion for the model target. -/
theorem isGroupLikeType :
    (preFrobenioid (Phi := Phi) (data := data)).IsGroupLikeType :=
  isGroupLike

/-- The Hom-colimit birational category is connected over a connected base. -/
theorem isConnected [IsConnected D] :
    @IsConnected
      (ColimitBirationalObject (Phi := Phi) (data := data))
      (ColimitBirationalObject.category (Phi := Phi) (data := data)) := by
  letI : IsConnected (BirationalObject (Phi := Phi) (data := data)) :=
    BirationalObject.isConnected
  exact isConnected_of_equivalent
    (comparisonEquivalence (Phi := Phi) (data := data)).symm

/-- Every Hom-colimit birational arrow is epic over a totally epimorphic base. -/
theorem epi
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) : Epi arrow := by
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  haveI : Epi (comparison.map arrow) :=
    BirationalObject.epi baseTotallyEpimorphic (comparison.map arrow)
  exact comparison.epi_of_epi_map inferInstance

/-- Proposition 4.4(ii)'s connected, totally epimorphic presentation data. -/
def preFrobenioidPresentation [IsConnected D]
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f) :
    PreFrobenioidPresentation where
  carrier := Cat.of (ColimitBirationalObject (Phi := Phi) (data := data))
  baseCategory := Cat.of D
  isFSM := IsFSM
  preFrobenioid := preFrobenioid (Phi := Phi) (data := data)
  carrierConnected := isConnected
  baseConnected := (inferInstance : IsConnected D)
  carrierTotallyEpimorphic := epi baseTotallyEpimorphic
  baseTotallyEpimorphic := baseTotallyEpimorphic

/-- Definition 4.5(i) model type for the canonical filtered-colimit target. -/
theorem isModelTypeForColimitBirationalization :
    (Carrier.preFrobenioid Phi data).IsModelType
      (preFrobenioid (Phi := Phi) (data := data))
      (localizationFunctor (Phi := Phi) (data := data)) :=
  ⟨Carrier.isPreModelType,
    fun object ↦ isFrobeniusNormalized ⟨object⟩⟩

end Carrier.ColimitBirationalObject

end

end Iut.SourceModelFrobenioid
