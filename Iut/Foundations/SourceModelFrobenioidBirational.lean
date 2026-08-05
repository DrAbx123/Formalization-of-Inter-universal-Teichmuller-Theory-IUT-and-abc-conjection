/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidPreModel

/-!
# Concrete birational category of the model Frobenioid

For the explicit model Frobenioid of Frobenioids I, Theorem 5.2, a birational
arrow is determined by its positive Frobenius degree, base arrow, and rational
function.  This file constructs that concrete category and proves the parts of
Proposition 4.4 and Theorem 5.2(ii) that can be checked directly in this model:
the original category embeds faithfully, pre-steps become isomorphisms, the
group of linear base-identity endomorphisms is the given rational-function
group, its divisor is `DivB`, and every object is Frobenius-normalized.

The identification of this concrete category with the filtered colimit over
co-angular pre-steps in Proposition 4.4 is deliberately not asserted here.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- The terminal divisorial monoid `0_D` in Proposition 4.4(i). -/
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

/-- The constant terminal divisorial monoid on the base category. -/
@[reducible] def zeroDivisorialMonoidOn : DivisorialMonoidOn D IsFSM where
  obj _ := zeroDivisorialAddMonoid
  pullback _ := 0
  pullback_id _ := by
    ext value
  pullback_comp _ _ := by
    ext value
  characteristicallyInjective _ _ _ _ := Subsingleton.elim _ _
  fsmPullbackIsIso _ _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
      fun value ↦ ⟨default, Subsingleton.elim _ _⟩⟩

/-- An object of the concrete model birational category. -/
structure BirationalObject where
  underlying : Carrier Phi data

/--
The degree, base arrow, and rational function that remain after birationalizing
a model-Frobenioid arrow.
-/
@[ext]
structure BirationalHom
    (source target : BirationalObject (Phi := Phi) (data := data)) where
  frobeniusDegree : ℕ+
  base : Object.base source.underlying ⟶ Object.base target.underlying
  rationalFunction : data.rationalFunctions.obj (Object.base source.underlying)

namespace BirationalHom

/-- Identity concrete birational arrow. -/
def id (source : BirationalObject (Phi := Phi) (data := data)) :
    BirationalHom source source where
  frobeniusDegree := 1
  base := 𝟙 (Object.base source.underlying)
  rationalFunction := 0

/-- Composition induced by the rational-function formula of Theorem 5.2(i). -/
def comp {source middle target : BirationalObject (Phi := Phi) (data := data)}
    (first : BirationalHom source middle) (second : BirationalHom middle target) :
    BirationalHom source target where
  frobeniusDegree := first.frobeniusDegree * second.frobeniusDegree
  base := first.base ≫ second.base
  rationalFunction :=
    data.rationalFunctions.pullback first.base second.rationalFunction +
      second.frobeniusDegree.val • first.rationalFunction

end BirationalHom

/-- Category structure on the concrete birational arrows. -/
instance birationalCategory :
    Category.{u} (BirationalObject (Phi := Phi) (data := data)) where
  Hom := BirationalHom
  id := BirationalHom.id
  comp := BirationalHom.comp
  id_comp arrow := by
    ext
    · simp [BirationalHom.comp, BirationalHom.id]
    · simp [BirationalHom.comp, BirationalHom.id]
    · change data.rationalFunctions.pullback (𝟙 _) arrow.rationalFunction +
          arrow.frobeniusDegree.val • 0 = arrow.rationalFunction
      rw [data.rationalFunctions.pullback_id]
      simp
  comp_id arrow := by
    ext
    · simp [BirationalHom.comp, BirationalHom.id]
    · simp [BirationalHom.comp, BirationalHom.id]
    · change data.rationalFunctions.pullback arrow.base 0 +
          1 • arrow.rationalFunction = arrow.rationalFunction
      rw [map_zero, zero_add, one_nsmul]
  assoc first second third := by
    ext
    · simp [BirationalHom.comp, mul_assoc]
    · simp [BirationalHom.comp, Category.assoc]
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

@[simp]
theorem birational_comp_rationalFunction
    {source middle target : BirationalObject (Phi := Phi) (data := data)}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).rationalFunction =
      data.rationalFunctions.pullback first.base second.rationalFunction +
        second.frobeniusDegree.val • first.rationalFunction :=
  rfl

/-- The groupified divisor attached to a concrete birational arrow. -/
def BirationalHom.divisorClass
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    Algebra.GrothendieckAddGroup
      (Phi.obj (Object.base source.underlying)).carrier :=
  gpPullback Phi arrow.base target.underlying.divisorClass +
    data.divisor (Object.base source.underlying) arrow.rationalFunction -
      arrow.frobeniusDegree.val • source.underlying.divisorClass

namespace BirationalObject

/-- Projection to the elementary Frobenioid for the zero monoid `0_D`. -/
def structureFunctor :
    BirationalObject (Phi := Phi) (data := data) ⥤
      ElementaryFrobenioid D IsFSM zeroDivisorialMonoidOn where
  obj object :=
    show ElementaryFrobenioid D IsFSM zeroDivisorialMonoidOn from
      @Object.base D categoryD IsFSM Phi object.underlying
  map arrow :=
    { base := arrow.base
      divisor := default
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := rfl
  map_comp _ _ := by
    apply ElementaryFrobenioidHom.ext
    · rfl
    · exact Subsingleton.elim _ _
    · rfl

/-- The concrete birational category as a pre-Frobenioid over `0_D`. -/
def preFrobenioid :
    PreFrobenioid (BirationalObject (Phi := Phi) (data := data)) D IsFSM where
  divisorMonoid := zeroDivisorialMonoidOn
  structureFunctor := structureFunctor

@[simp]
theorem preFrobenioid_frobeniusDegree
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).frobeniusDegree arrow =
      arrow.frobeniusDegree :=
  rfl

@[simp]
theorem preFrobenioid_base_map
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    (preFrobenioid (Phi := Phi) (data := data)).base.map arrow = arrow.base :=
  rfl

/-- The natural functor from the model Frobenioid to the concrete target. -/
def inclusionFunctor :
    Carrier Phi data ⥤ BirationalObject (Phi := Phi) (data := data) where
  obj object := ⟨object⟩
  map arrow :=
    { frobeniusDegree := arrow.frobeniusDegree
      base := arrow.base
      rationalFunction := arrow.rationalFunction }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The concrete birational inclusion is faithful, as in Proposition 4.4(ii). -/
theorem inclusionFunctor_faithful :
    (inclusionFunctor (Phi := Phi) (data := data)).Faithful := by
  constructor
  intro source target first second equality
  have degreeEquality := congrArg BirationalHom.frobeniusDegree equality
  have baseEquality := congrArg BirationalHom.base equality
  have rationalFunctionEquality :=
    congrArg BirationalHom.rationalFunction equality
  change first.frobeniusDegree = second.frobeniusDegree at degreeEquality
  change first.base = second.base at baseEquality
  change first.rationalFunction = second.rationalFunction at rationalFunctionEquality
  apply Iut.SourceModelFrobenioid.Hom.ext degreeEquality baseEquality
  · have firstBalance := first.balance
    rw [degreeEquality, baseEquality, rationalFunctionEquality] at firstBalance
    have representedEquality := add_left_cancel
      (firstBalance.trans second.balance.symm)
    let M := Phi.obj (Object.base source)
    letI : IsLeftCancelAdd M.carrier :=
      ⟨fun a b c equality ↦ M.integral a b c equality⟩
    letI : IsCancelAdd M.carrier :=
      AddCommMagma.IsLeftCancelAdd.toIsCancelAdd M.carrier
    exact Algebra.GrothendieckAddGroup.of_injective representedEquality
  · exact rationalFunctionEquality

/-- The concrete birational category is connected over a connected base. -/
theorem isConnected [IsConnected D] :
    @IsConnected (BirationalObject (Phi := Phi) (data := data))
      (birationalCategory (Phi := Phi) (data := data)) := by
  letI : Nonempty (BirationalObject (Phi := Phi) (data := data)) :=
    ⟨⟨Carrier.zeroObject Phi data (Classical.arbitrary D)⟩⟩
  apply IsConnected.of_constant_of_preserves_morphisms
  intro alpha value preserves first second
  letI : IsConnected (Carrier Phi data) := Carrier.isConnected Phi data
  exact CategoryTheory.constant_of_preserves_morphisms
    (fun object : Carrier Phi data ↦ value ⟨object⟩)
    (fun source target arrow ↦ preserves
      ((inclusionFunctor (Phi := Phi) (data := data)).map arrow))
    first.underlying second.underlying

/-- Every concrete birational arrow is epic over a totally epimorphic base. -/
theorem epi
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) : Epi arrow := by
  constructor
  intro next first second equality
  letI : Epi arrow.base := baseTotallyEpimorphic arrow.base
  have degreeEquality :
      first.frobeniusDegree = second.frobeniusDegree := by
    have projected := congrArg BirationalHom.frobeniusDegree equality
    change arrow.frobeniusDegree * first.frobeniusDegree =
      arrow.frobeniusDegree * second.frobeniusDegree at projected
    exact mul_left_cancel projected
  have baseEquality : first.base = second.base := by
    have projected := congrArg BirationalHom.base equality
    change arrow.base ≫ first.base = arrow.base ≫ second.base at projected
    exact (cancel_epi arrow.base).mp projected
  have rationalFunctionEquality :
      first.rationalFunction = second.rationalFunction := by
    have projected := congrArg BirationalHom.rationalFunction equality
    change data.rationalFunctions.pullback arrow.base first.rationalFunction +
          first.frobeniusDegree.val • arrow.rationalFunction =
        data.rationalFunctions.pullback arrow.base second.rationalFunction +
          second.frobeniusDegree.val • arrow.rationalFunction at projected
    rw [degreeEquality] at projected
    apply data.rationalFunctions.pullback_injective arrow.base
    exact add_right_cancel projected
  exact BirationalHom.ext degreeEquality baseEquality rationalFunctionEquality

/--
Inclusion recovers the original effective divisor after groupification.
-/
theorem inclusionFunctor_map_divisorClass
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    ((inclusionFunctor (Phi := Phi) (data := data)).map arrow).divisorClass =
      Algebra.GrothendieckAddGroup.of arrow.divisor := by
  dsimp [BirationalHom.divisorClass, inclusionFunctor]
  have balance := arrow.balance
  rw [← balance]
  abel

/-- Inverse of a linear concrete arrow whose base projection is invertible. -/
def inverse {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (baseIsIso : IsIso arrow.base) :
    target ⟶ source := by
  letI : IsIso arrow.base := baseIsIso
  exact
    { frobeniusDegree := 1
      base := inv arrow.base
      rationalFunction :=
        -(data.rationalFunctions.pullback (inv arrow.base)
          arrow.rationalFunction) }

theorem hom_inverse {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (linear : arrow.frobeniusDegree = 1)
    (baseIsIso : IsIso arrow.base) :
    arrow ≫ inverse arrow baseIsIso = 𝟙 source := by
  letI : IsIso arrow.base := baseIsIso
  apply BirationalHom.ext
  · change arrow.frobeniusDegree * 1 = 1
    rw [linear]
    rfl
  · change arrow.base ≫ inv arrow.base = 𝟙 _
    exact IsIso.hom_inv_id arrow.base
  · change data.rationalFunctions.pullback arrow.base
        (-(data.rationalFunctions.pullback (inv arrow.base)
          arrow.rationalFunction)) + 1 • arrow.rationalFunction = 0
    rw [map_neg, ← AddMonoidHom.comp_apply,
      ← data.rationalFunctions.pullback_comp,
      IsIso.hom_inv_id, data.rationalFunctions.pullback_id]
    rw [AddMonoidHom.id_apply, one_nsmul, neg_add_cancel]

theorem inverse_hom {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (linear : arrow.frobeniusDegree = 1)
    (baseIsIso : IsIso arrow.base) :
    inverse arrow baseIsIso ≫ arrow = 𝟙 target := by
  letI : IsIso arrow.base := baseIsIso
  apply BirationalHom.ext
  · change 1 * arrow.frobeniusDegree = 1
    rw [linear]
    rfl
  · change inv arrow.base ≫ arrow.base = 𝟙 _
    exact IsIso.inv_hom_id arrow.base
  · change data.rationalFunctions.pullback (inv arrow.base)
        arrow.rationalFunction + arrow.frobeniusDegree.val •
          (-(data.rationalFunctions.pullback (inv arrow.base)
            arrow.rationalFunction)) = 0
    rw [linear]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    exact add_neg_cancel _

/-- A linear arrow over a base isomorphism is an isomorphism in the target. -/
def isoOfLinearBaseIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (linear : arrow.frobeniusDegree = 1)
    (baseIsIso : IsIso arrow.base) : source ≅ target where
  hom := arrow
  inv := inverse arrow baseIsIso
  hom_inv_id := hom_inverse arrow linear baseIsIso
  inv_hom_id := inverse_hom arrow linear baseIsIso

/-- Every model pre-step becomes invertible in the concrete target. -/
theorem inclusion_map_isIso_of_preStep
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (Carrier.preFrobenioid Phi data).IsPreStep arrow) :
    IsIso ((inclusionFunctor (Phi := Phi) (data := data)).map arrow) := by
  let mapped := (inclusionFunctor (Phi := Phi) (data := data)).map arrow
  have baseIsIso := preStep.2
  change IsIso arrow.base at baseIsIso
  exact (isoOfLinearBaseIso mapped preStep.1 baseIsIso).isIso_hom

/-- A rational function as a linear base-identity endomorphism. -/
def rationalFunctionEndomorphism
    (object : BirationalObject (Phi := Phi) (data := data))
    (value : Multiplicative
      (data.rationalFunctions.obj (Object.base object.underlying))) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
      object where
  hom :=
    { frobeniusDegree := 1
      base := 𝟙 (Object.base object.underlying)
      rationalFunction := value.toAdd }
  linear := by
    dsimp [PreFrobenioid.IsLinear, PreFrobenioid.frobeniusDegree,
      preFrobenioid, structureFunctor]
  baseIdentity := by
    dsimp [PreFrobenioid.IsBaseIdentity, preFrobenioid, structureFunctor]
    rfl

/-- The rational-function isomorphism asserted in Theorem 5.2(ii), objectwise. -/
def rationalFunctionEquiv
    (object : BirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object ≃*
      Multiplicative (data.rationalFunctions.obj (Object.base object.underlying)) where
  toFun alpha := Multiplicative.ofAdd alpha.hom.rationalFunction
  invFun := rationalFunctionEndomorphism object
  left_inv alpha := by
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    apply BirationalHom.ext
    · have linear := alpha.linear
      dsimp [PreFrobenioid.IsLinear, preFrobenioid, structureFunctor] at linear
      exact linear.symm
    · have baseIdentity := alpha.baseIdentity
      dsimp [PreFrobenioid.IsBaseIdentity, preFrobenioid,
        structureFunctor] at baseIdentity
      exact baseIdentity.symm
    · rfl
  right_inv value := rfl
  map_mul' left right := by
    congr 1
    change (left * right).hom.rationalFunction =
      left.hom.rationalFunction + right.hom.rationalFunction
    change data.rationalFunctions.pullback left.hom.base
          right.hom.rationalFunction +
        right.hom.frobeniusDegree.val • left.hom.rationalFunction = _
    have leftBase := left.baseIdentity
    change left.hom.base = 𝟙 _ at leftBase
    have rightLinear := right.linear
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftBase, rightLinear, data.rationalFunctions.pullback_id]
    change right.hom.rationalFunction + (1 : ℕ) • left.hom.rationalFunction = _
    rw [one_nsmul]
    abel

/-- Under the rational-function equivalence, the birational divisor is `DivB`. -/
theorem rationalFunctionEndomorphism_divisorClass
    (object : BirationalObject (Phi := Phi) (data := data))
    (value : Multiplicative
      (data.rationalFunctions.obj (Object.base object.underlying))) :
    (rationalFunctionEndomorphism object value).hom.divisorClass =
      data.divisor (Object.base object.underlying) value.toAdd := by
  dsimp [rationalFunctionEndomorphism, BirationalHom.divisorClass]
  rw [gpPullback_id]
  change object.underlying.divisorClass + _ -
      (1 : ℕ) • object.underlying.divisorClass = _
  rw [one_nsmul]
  abel

/-- Rational functions of a power add by the corresponding natural multiple. -/
theorem rationalFunction_pow
    (object : BirationalObject (Phi := Phi) (data := data))
    (alpha :
      (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        object)
    (degree : ℕ) :
    (alpha ^ degree).hom.rationalFunction =
      degree • alpha.hom.rationalFunction := by
  have mapped := map_pow (rationalFunctionEquiv object) alpha degree
  exact congrArg Multiplicative.toAdd mapped

/-- Every object of the concrete model birational category is normalized. -/
theorem isFrobeniusNormalized
    (object : BirationalObject (Phi := Phi) (data := data)) :
    (preFrobenioid (Phi := Phi) (data := data)).IsFrobeniusNormalized
      object := by
  intro phi phiBase alpha
  change phi ≫ (alpha ^ phi.frobeniusDegree.val).hom =
    alpha.hom ≫ phi
  apply BirationalHom.ext
  · have alphaPowerLinear :=
      (alpha ^ phi.frobeniusDegree.val).linear
    change (alpha ^ phi.frobeniusDegree.val).hom.frobeniusDegree = 1 at alphaPowerLinear
    have alphaLinear := alpha.linear
    change alpha.hom.frobeniusDegree = 1 at alphaLinear
    change phi.frobeniusDegree *
        (alpha ^ phi.frobeniusDegree.val).hom.frobeniusDegree =
      alpha.hom.frobeniusDegree * phi.frobeniusDegree
    rw [alphaPowerLinear, alphaLinear]
    simp
  · have alphaPowerBase := (alpha ^ phi.frobeniusDegree.val).baseIdentity
    change (alpha ^ phi.frobeniusDegree.val).hom.base = 𝟙 _ at alphaPowerBase
    have alphaBase := alpha.baseIdentity
    change alpha.hom.base = 𝟙 _ at alphaBase
    change phi.base = 𝟙 _ at phiBase
    change phi.base ≫ (alpha ^ phi.frobeniusDegree.val).hom.base =
      alpha.hom.base ≫ phi.base
    rw [phiBase, alphaBase, alphaPowerBase]
  · rw [birational_comp_rationalFunction,
      birational_comp_rationalFunction]
    have alphaPowerLinear :=
      (alpha ^ phi.frobeniusDegree.val).linear
    change (alpha ^ phi.frobeniusDegree.val).hom.frobeniusDegree = 1 at alphaPowerLinear
    rw [alphaPowerLinear]
    change data.rationalFunctions.pullback phi.base
          (alpha ^ phi.frobeniusDegree.val).hom.rationalFunction +
        1 • phi.rationalFunction =
      data.rationalFunctions.pullback alpha.hom.base phi.rationalFunction +
        phi.frobeniusDegree.val • alpha.hom.rationalFunction
    have phiBase' := phiBase
    change phi.base = 𝟙 _ at phiBase'
    have alphaBase := alpha.baseIdentity
    change alpha.hom.base = 𝟙 _ at alphaBase
    rw [phiBase', alphaBase,
      data.rationalFunctions.pullback_id,
      rationalFunction_pow]
    simp only [AddMonoidHom.id_apply, one_nsmul]
    abel

/-- The concrete model birational category is Frobenius-normalized. -/
theorem isFrobeniusNormalizedType :
    (preFrobenioid (Phi := Phi) (data := data)).IsFrobeniusNormalizedType :=
  isFrobeniusNormalized

/--
The model Frobenioid is pre-model and normalized after passage to the concrete
birational target.  Identifying this target with Proposition 4.4's colimit is
the remaining step before this theorem discharges source model type.
-/
theorem isModelTypeForConcreteBirationalization :
    (Carrier.preFrobenioid Phi data).IsModelType
      (preFrobenioid (Phi := Phi) (data := data))
      (inclusionFunctor (Phi := Phi) (data := data)) :=
  ⟨Carrier.isPreModelType,
    fun object ↦ isFrobeniusNormalized ⟨object⟩⟩

end BirationalObject

end

end Iut.SourceModelFrobenioid
