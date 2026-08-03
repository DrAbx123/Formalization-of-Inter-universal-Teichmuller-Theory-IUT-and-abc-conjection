/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidBirationalDivisor

/-!
# Definition 1.3 for the concrete birational model

This file proves the seven axiom groups of Frobenioids I, Definition 1.3, for
the concrete group-like birational target used in Proposition 4.4.  The zero
divisor monoid makes every arrow isometric and co-angular, but the existence
and uniqueness clauses are retained as explicit categorical constructions.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid.BirationalObject

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

private abbrev P := preFrobenioid (Phi := Phi) (data := data)

/-- The object over a base object used in Definition 1.3(i)(a). -/
def zeroObject (base : D) : BirationalObject (Phi := Phi) (data := data) :=
  ⟨Carrier.zeroObject Phi data base⟩

/-- The canonical birational Frobenius endomorphism of any object. -/
def frobeniusHom
    (object : BirationalObject (Phi := Phi) (data := data)) (degree : ℕ+) :
    object ⟶ object where
  frobeniusDegree := degree
  base := 𝟙 _
  rationalFunction := 0

/-- Every object in the group-like target is Frobenius-trivial. -/
def frobeniusTrivialization
    (object : BirationalObject (Phi := Phi) (data := data)) :
    P.FrobeniusTrivialization object where
  lift := frobeniusHom object
  map_one := rfl
  map_mul m n := by
    apply BirationalHom.ext <;> simp [frobeniusHom]
  degree_section _ := rfl
  base_identity _ := rfl
  of_frobenius_type degree := by
    apply (isOfFrobeniusType_iff_isBaseIso (frobeniusHom object degree)).2
    change IsIso (𝟙 _)
    infer_instance

/-- Definition 1.3(i)(a) for the concrete birational target. -/
theorem baseRepresented (base : D) :
    ∃ object : BirationalObject (Phi := Phi) (data := data),
      P.IsFrobeniusTrivial object ∧ Nonempty (P.base.obj object ≅ base) :=
  ⟨zeroObject base, ⟨frobeniusTrivialization (zeroObject base)⟩,
    ⟨Iso.refl base⟩⟩

/-- Definition 1.3(i)(b): two objects over isomorphic bases have common pre-steps. -/
def commonPreSteps
    (left right : BirationalObject (Phi := Phi) (data := data))
    (baseIso : P.base.obj left ≅ P.base.obj right) :
    P.CommonPreStepWitness left right baseIso where
  midpoint := left
  toLeft := 𝟙 left
  toRight :=
    { frobeniusDegree := 1
      base := baseIso.hom
      rationalFunction := 0 }
  toLeft_preStep := by
    rw [← isIso_iff_isPreStep]
    infer_instance
  toRight_preStep := by
    rw [← isIso_iff_isPreStep]
    exact (isoOfLinearBaseIso _ rfl inferInstance).isIso_hom
  leftBaseInverse := 𝟙 _
  leftBaseInverse_hom := by change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
  hom_leftBaseInverse := by change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
  comparison := by simp

/-- A pullback arrow realizing an arbitrary object of the base slice. -/
def baseSliceLift
    (object : BirationalObject (Phi := Phi) (data := data))
    (value : P.BaseSliceObject object) :
    PreFrobenioid.PullbackSliceObject object where
  source := zeroObject value.source
  hom :=
    { frobeniusDegree := 1
      base := value.hom
      rationalFunction := 0 }

theorem baseSliceLift_isPullback
    (object : BirationalObject (Phi := Phi) (data := data))
    (value : P.BaseSliceObject object) :
    P.IsPullback (baseSliceLift object value).hom :=
  (isPullback_iff_isLinear _).2 rfl

/-- A base-slice map has a unique lift between pullback slices. -/
def pullbackSlicePreimage
    (object : BirationalObject (Phi := Phi) (data := data))
    (left right : PreFrobenioid.PullbackSliceObject object)
    (_leftPullback : P.IsPullback left.hom)
    (rightPullback : P.IsPullback right.hom)
    (value : P.BaseSliceHom (left.toBase P) (right.toBase P)) :
    PreFrobenioid.PullbackSliceHom left right := by
  let comparison : P.PullbackComparisonTarget right.hom left.source :=
    { toCodomain := left.hom
      toBaseDomain := value.hom
      commutes := value.commutes.symm }
  let lift := Classical.choose ((rightPullback left.source).2 comparison)
  have liftComparison :=
    Classical.choose_spec ((rightPullback left.source).2 comparison)
  exact
    { hom := lift
      commutes := congrArg
        PreFrobenioid.PullbackComparisonTarget.toCodomain liftComparison }

theorem baseSliceHom_ext
    {object : BirationalObject (Phi := Phi) (data := data)}
    {left right : P.BaseSliceObject object}
    {first second : P.BaseSliceHom left right}
    (homEquality : first.hom = second.hom) : first = second := by
  cases first
  cases second
  cases homEquality
  rfl

theorem pullbackSlicePreimage_toBase
    (object : BirationalObject (Phi := Phi) (data := data))
    (left right : PreFrobenioid.PullbackSliceObject object)
    (leftPullback : P.IsPullback left.hom)
    (rightPullback : P.IsPullback right.hom)
    (value : P.BaseSliceHom (left.toBase P) (right.toBase P)) :
    (pullbackSlicePreimage object left right leftPullback rightPullback value).toBase P =
      value := by
  have homEquality := congrArg
      PreFrobenioid.PullbackComparisonTarget.toBaseDomain
    (Classical.choose_spec ((rightPullback left.source).2
      { toCodomain := left.hom
        toBaseDomain := value.hom
        commutes := value.commutes.symm }))
  apply baseSliceHom_ext
  exact homEquality

theorem pullbackSliceProjection_bijective
    (object : BirationalObject (Phi := Phi) (data := data))
    (left right : PreFrobenioid.PullbackSliceObject object)
    (leftPullback : P.IsPullback left.hom)
    (rightPullback : P.IsPullback right.hom) :
    Function.Bijective
      (fun value : PreFrobenioid.PullbackSliceHom left right ↦ value.toBase P) := by
  constructor
  · intro first second equality
    cases first with
    | mk first firstCommutes =>
      cases second with
      | mk second secondCommutes =>
        congr 1
        have baseEquality : first.base = second.base :=
          congrArg PreFrobenioid.BaseSliceHom.hom equality
        have compositeEquality : first ≫ right.hom = second ≫ right.hom :=
          firstCommutes.trans secondCommutes.symm
        apply BirationalHom.ext
        · have projected := congrArg BirationalHom.frobeniusDegree compositeEquality
          change first.frobeniusDegree * right.hom.frobeniusDegree =
            second.frobeniusDegree * right.hom.frobeniusDegree at projected
          have rightLinear := (isPullback_iff_isLinear right.hom).1 rightPullback
          change right.hom.frobeniusDegree = 1 at rightLinear
          simpa [rightLinear] using projected
        · exact baseEquality
        · have projected := congrArg BirationalHom.rationalFunction compositeEquality
          change data.rationalFunctions.pullback first.base right.hom.rationalFunction +
                right.hom.frobeniusDegree.val • first.rationalFunction =
              data.rationalFunctions.pullback second.base right.hom.rationalFunction +
                right.hom.frobeniusDegree.val • second.rationalFunction at projected
          have rightLinear := (isPullback_iff_isLinear right.hom).1 rightPullback
          change right.hom.frobeniusDegree = 1 at rightLinear
          rw [baseEquality, rightLinear] at projected
          simpa only [PNat.val_ofNat, one_nsmul] using add_left_cancel projected
  · intro value
    refine ⟨pullbackSlicePreimage object left right leftPullback rightPullback value, ?_⟩
    exact pullbackSlicePreimage_toBase object left right leftPullback
      rightPullback value

/-- Definition 1.3(i)(c) for the concrete birational target. -/
def pullbackBaseSlices
    (object : BirationalObject (Phi := Phi) (data := data)) :
    P.PullbackBaseSliceEquivalence object where
  essentiallySurjective value :=
    ⟨baseSliceLift object value, baseSliceLift_isPullback object value,
      ⟨{
        iso := Iso.refl value.source
        hom_commutes := by
          change 𝟙 value.source ≫ value.hom = value.hom
          simp
      }⟩⟩
  fullyFaithful left right leftPullback rightPullback :=
    pullbackSliceProjection_bijective object left right leftPullback rightPullback

/-- Definition 1.3(ii)'s canonical degree witness. -/
def frobeniusDegreeWitness
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    (object : BirationalObject (Phi := Phi) (data := data)) (degree : ℕ+) :
    P.FrobeniusDegreeWitness object degree where
  codomain := object
  hom := frobeniusHom object degree
  ofFrobeniusType :=
    (isOfFrobeniusType_iff_isBaseIso _).2 (by
      change IsIso (𝟙 _)
      infer_instance)
  degree := rfl
  essentiallyUnique := by
    intro target arrow arrowType arrowDegree
    have baseIsIso : IsIso arrow.base :=
      (isOfFrobeniusType_iff_isBaseIso arrow).1 arrowType
    let comparison : object ⟶ target :=
      { frobeniusDegree := 1
        base := arrow.base
        rationalFunction := arrow.rationalFunction }
    let comparisonIso : object ≅ target :=
      isoOfLinearBaseIso comparison rfl baseIsIso
    have comparisonHom : comparisonIso.hom = comparison := rfl
    have comparisonComp : frobeniusHom object degree ≫ comparisonIso.hom = arrow := by
      rw [comparisonHom]
      apply BirationalHom.ext
      · change degree * 1 = arrow.frobeniusDegree
        simpa using arrowDegree.symm
      · change 𝟙 _ ≫ arrow.base = arrow.base
        simp
      · change data.rationalFunctions.pullback (𝟙 _) arrow.rationalFunction +
            1 • (0 : data.rationalFunctions.obj _) = arrow.rationalFunction
        rw [data.rationalFunctions.pullback_id]
        simp
    refine ⟨comparisonIso, ?_, ?_⟩
    · exact comparisonComp
    · intro candidate candidateComp
      apply Iso.ext
      letI : Epi (frobeniusHom object degree) :=
        epi baseTotallyEpimorphic (frobeniusHom object degree)
      apply (cancel_epi (frobeniusHom object degree)).mp
      exact candidateComp.trans comparisonComp.symm

/-- Transport of `O^bullet` along a birational base isomorphism. -/
def baseIsoTransport
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (baseIso : Object.base source.underlying ≅ Object.base target.underlying)
    (alpha : P.LinearBaseIdentityEndomorphism source) :
    P.LinearBaseIdentityEndomorphism target where
  hom :=
    { frobeniusDegree := 1
      base := 𝟙 _
      rationalFunction := data.rationalFunctions.pullback baseIso.inv
        alpha.hom.rationalFunction }
  linear := rfl
  baseIdentity := rfl

def baseIsoTransportEquiv
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (baseIso : Object.base source.underlying ≅ Object.base target.underlying) :
    P.LinearBaseIdentityEndomorphism source ≃*
      P.LinearBaseIdentityEndomorphism target where
  toFun := baseIsoTransport baseIso
  invFun := baseIsoTransport baseIso.symm
  left_inv alpha := by
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    apply BirationalHom.ext
    · exact alpha.linear.symm
    · exact alpha.baseIdentity.symm
    · change data.rationalFunctions.pullback baseIso.hom
          (data.rationalFunctions.pullback baseIso.inv alpha.hom.rationalFunction) =
        alpha.hom.rationalFunction
      rw [← AddMonoidHom.comp_apply, ← data.rationalFunctions.pullback_comp,
        baseIso.hom_inv_id, data.rationalFunctions.pullback_id]
      rfl
  right_inv alpha := by
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    apply BirationalHom.ext
    · exact alpha.linear.symm
    · exact alpha.baseIdentity.symm
    · change data.rationalFunctions.pullback baseIso.inv
          (data.rationalFunctions.pullback baseIso.hom alpha.hom.rationalFunction) =
        alpha.hom.rationalFunction
      rw [← AddMonoidHom.comp_apply, ← data.rationalFunctions.pullback_comp,
        baseIso.inv_hom_id, data.rationalFunctions.pullback_id]
      rfl
  map_mul' left right := by
    apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
    apply BirationalHom.ext
    · rfl
    · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      simp
    · change data.rationalFunctions.pullback baseIso.inv
          (data.rationalFunctions.pullback left.hom.base right.hom.rationalFunction +
            right.hom.frobeniusDegree.val • left.hom.rationalFunction) = _
      have leftBase := left.baseIdentity
      have rightLinear := right.linear
      change left.hom.base = 𝟙 _ at leftBase
      change right.hom.frobeniusDegree = 1 at rightLinear
      rw [leftBase, rightLinear, data.rationalFunctions.pullback_id]
      simp only [AddMonoidHom.id_apply, PNat.val_ofNat, one_nsmul, map_add]
      change _ = data.rationalFunctions.pullback (𝟙 _)
          (data.rationalFunctions.pullback baseIso.inv right.hom.rationalFunction) +
          1 • data.rationalFunctions.pullback baseIso.inv left.hom.rationalFunction
      rw [data.rationalFunctions.pullback_id]
      simp only [AddMonoidHom.id_apply, one_nsmul]

/-- Definition 1.3(iii)(c)'s unit transport. -/
def preStepBaseIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (preStep : P.IsPreStep arrow) :
    Object.base source.underlying ≅ Object.base target.underlying := by
  have baseIsIso := preStep.2
  change IsIso arrow.base at baseIsIso
  letI : IsIso arrow.base := baseIsIso
  exact asIso arrow.base

def unitTransport
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (preStep : P.IsPreStep arrow) :
    P.CoAngularUnitTransport arrow where
  transport := baseIsoTransportEquiv (preStepBaseIso arrow preStep)
  conjugates alpha := by
    have linear := preStep.1
    have baseIsIso := preStep.2
    change IsIso arrow.base at baseIsIso
    letI : IsIso arrow.base := baseIsIso
    change arrow.frobeniusDegree = 1 at linear
    have alphaLinear := alpha.linear
    change alpha.hom.frobeniusDegree = 1 at alphaLinear
    have alphaBase := alpha.baseIdentity
    change alpha.hom.base = 𝟙 _ at alphaBase
    dsimp only [baseIsoTransportEquiv, baseIsoTransport, preStepBaseIso]
    apply BirationalHom.ext
    · change alpha.hom.frobeniusDegree * arrow.frobeniusDegree =
        arrow.frobeniusDegree * 1
      rw [linear, alphaLinear]
    · change alpha.hom.base ≫ arrow.base = arrow.base ≫ 𝟙 _
      rw [alphaBase]
      simp
    · change data.rationalFunctions.pullback alpha.hom.base arrow.rationalFunction +
          arrow.frobeniusDegree.val • alpha.hom.rationalFunction =
        data.rationalFunctions.pullback arrow.base
            (data.rationalFunctions.pullback (inv arrow.base)
              alpha.hom.rationalFunction) +
          (1 : ℕ+).val • arrow.rationalFunction
      rw [alphaBase, linear, data.rationalFunctions.pullback_id,
        ← AddMonoidHom.comp_apply, ← data.rationalFunctions.pullback_comp,
        IsIso.hom_inv_id, data.rationalFunctions.pullback_id]
      simp only [AddMonoidHom.id_apply, PNat.val_ofNat, one_nsmul]
      abel

theorem unitTransport_unique
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (left right : P.CoAngularUnitTransport arrow) :
    left = right := by
  cases left with
  | mk left leftConjugates =>
    cases right with
    | mk right rightConjugates =>
      congr 1
      apply MulEquiv.ext
      intro alpha
      apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
      letI : Epi arrow := epi baseTotallyEpimorphic arrow
      apply (cancel_epi arrow).mp
      exact (leftConjugates alpha).symm.trans (rightConjugates alpha)

theorem unitTransport_dependsOnlyOnBase
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (left right : source ⟶ target) (leftPreStep : P.IsPreStep left)
    (rightPreStep : P.IsPreStep right) (baseEquality : left.base = right.base) :
    (unitTransport left leftPreStep).transport =
      (unitTransport right rightPreStep).transport := by
  change baseIsoTransportEquiv (preStepBaseIso left leftPreStep) =
    baseIsoTransportEquiv (preStepBaseIso right rightPreStep)
  congr 1
  apply Iso.ext
  exact baseEquality

/-- The unique outgoing representative of the sole divisor in `0_D`. -/
def outgoingDivisorRepresentative
    (object : BirationalObject (Phi := Phi) (data := data))
    (divisor : P.DivisorOrder object) :
    P.OutgoingCoAngularPreStep object divisor where
  target := object
  hom := 𝟙 object
  preStep := by rw [← isIso_iff_isPreStep]; infer_instance
  coAngular := isCoAngular _
  divisor_eq := by cases divisor; rfl

theorem outgoingDivisorOrderFullyFaithful
    {object : BirationalObject (Phi := Phi) (data := data)}
    {leftDivisor rightDivisor : P.DivisorOrder object}
    (left : P.OutgoingCoAngularPreStep object leftDivisor)
    (right : P.OutgoingCoAngularPreStep object rightDivisor) :
    leftDivisor ≤ rightDivisor ↔
      ∃! arrow : left.target ⟶ right.target,
        left.hom ≫ arrow = right.hom := by
  constructor
  · intro _
    haveI : IsIso left.hom := isIso_of_isPreStep left.hom left.preStep
    refine ⟨inv left.hom ≫ right.hom, by simp, ?_⟩
    intro arrow equality
    apply (cancel_epi left.hom).mp
    simpa using equality
  · intro _
    exact ⟨0, by cases leftDivisor; cases rightDivisor; rfl⟩

theorem outgoingDivisorRepresentative_unique
    {object : BirationalObject (Phi := Phi) (data := data)}
    {divisor : P.DivisorOrder object}
    (left right : P.OutgoingCoAngularPreStep object divisor) :
    ∃! iso : left.target ≅ right.target,
      left.hom ≫ iso.hom = right.hom := by
  haveI : IsIso left.hom := isIso_of_isPreStep left.hom left.preStep
  haveI : IsIso right.hom := isIso_of_isPreStep right.hom right.preStep
  let iso := (asIso left.hom).symm ≪≫ asIso right.hom
  refine ⟨iso, by simp [iso], ?_⟩
  intro candidate equality
  apply Iso.ext
  apply (cancel_epi left.hom).mp
  simpa [iso] using equality

theorem incomingDivisor
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    ∃! divisor : P.DivisorOrder target,
      P.divisorMonoid.pullback (P.base.map arrow) divisor = P.divisor arrow := by
  refine ⟨PUnit.unit, by rfl, ?_⟩
  intro value _
  cases value
  rfl

/-- The unique incoming representative of the sole divisor in `0_D`. -/
def incomingDivisorRepresentative
    (object : BirationalObject (Phi := Phi) (data := data))
    (divisor : P.DivisorOrder object) :
    P.IncomingCoAngularPreStep object divisor where
  source := object
  hom := 𝟙 object
  preStep := by rw [← isIso_iff_isPreStep]; infer_instance
  coAngular := isCoAngular _
  pulledBack_divisor_eq := by cases divisor; rfl

theorem incomingDivisorOrderFullyFaithful
    {object : BirationalObject (Phi := Phi) (data := data)}
    {leftDivisor rightDivisor : P.DivisorOrder object}
    (left : P.IncomingCoAngularPreStep object leftDivisor)
    (right : P.IncomingCoAngularPreStep object rightDivisor) :
    rightDivisor ≤ leftDivisor ↔
      ∃! arrow : left.source ⟶ right.source,
        arrow ≫ right.hom = left.hom := by
  constructor
  · intro _
    haveI : IsIso right.hom := isIso_of_isPreStep right.hom right.preStep
    refine ⟨left.hom ≫ inv right.hom, by simp, ?_⟩
    intro arrow equality
    apply (cancel_mono right.hom).mp
    simpa using equality
  · intro _
    exact ⟨0, by cases leftDivisor; cases rightDivisor; rfl⟩

theorem incomingDivisorRepresentative_unique
    {object : BirationalObject (Phi := Phi) (data := data)}
    {divisor : P.DivisorOrder object}
    (left right : P.IncomingCoAngularPreStep object divisor) :
    ∃! iso : left.source ≅ right.source,
      iso.hom ≫ right.hom = left.hom := by
  haveI : IsIso left.hom := isIso_of_isPreStep left.hom left.preStep
  haveI : IsIso right.hom := isIso_of_isPreStep right.hom right.preStep
  let iso := asIso left.hom ≪≫ (asIso right.hom).symm
  refine ⟨iso, by simp [iso], ?_⟩
  intro candidate equality
  apply Iso.ext
  apply (cancel_mono right.hom).mp
  simpa [iso] using equality

/-- The literal Frobenius/pre-step/pullback factorization of a target arrow. -/
def factorization
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) : P.FrobenioidFactorization arrow where
  frobeniusCodomain := source
  preStepCodomain := source
  frobenius := frobeniusHom source arrow.frobeniusDegree
  preStep :=
    { frobeniusDegree := 1
      base := 𝟙 _
      rationalFunction := arrow.rationalFunction }
  pullback :=
    { frobeniusDegree := 1
      base := arrow.base
      rationalFunction := 0 }
  frobenius_type := (isOfFrobeniusType_iff_isBaseIso _).2 (by
    change IsIso (𝟙 _)
    infer_instance)
  preStep_type := by
    rw [← isIso_iff_isPreStep]
    exact (isoOfLinearBaseIso _ rfl inferInstance).isIso_hom
  pullback_type := (isPullback_iff_isLinear _).2 rfl
  composite := by
    apply BirationalHom.ext
    · simp [frobeniusHom]
    · simp [frobeniusHom]
    · change data.rationalFunctions.pullback (𝟙 _)
          (data.rationalFunctions.pullback (𝟙 _) 0 +
            (1 : ℕ) • arrow.rationalFunction) +
          (1 : ℕ) • (0 : data.rationalFunctions.obj _) = arrow.rationalFunction
      simp only [map_zero, zero_add, one_nsmul, add_zero]
      exact DFunLike.congr_fun
        (data.rationalFunctions.pullback_id (Object.base source.underlying))
        arrow.rationalFunction

/-- The comparison of Frobenius codomains in two factorizations. -/
def factorizationFrobeniusIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} (left right : P.FrobenioidFactorization arrow) :
    left.frobeniusCodomain ≅ right.frobeniusCodomain := by
  have leftBaseIsIso : IsIso left.frobenius.base :=
    (isOfFrobeniusType_iff_isBaseIso left.frobenius).1 left.frobenius_type
  letI : IsIso left.frobenius.base := leftBaseIsIso
  let hom : left.frobeniusCodomain ⟶ right.frobeniusCodomain :=
    { frobeniusDegree := 1
      base := inv left.frobenius.base ≫ right.frobenius.base
      rationalFunction := data.rationalFunctions.pullback (inv left.frobenius.base)
        (right.frobenius.rationalFunction - left.frobenius.rationalFunction) }
  have homBaseIsIso : IsIso hom.base := by
    dsimp [hom]
    have rightBaseIsIso : IsIso right.frobenius.base :=
      (isOfFrobeniusType_iff_isBaseIso right.frobenius).1 right.frobenius_type
    letI : IsIso right.frobenius.base := rightBaseIsIso
    infer_instance
  exact isoOfLinearBaseIso hom rfl homBaseIsIso

theorem factorization_frobenius_square
    {source target : BirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} (left right : P.FrobenioidFactorization arrow) :
    left.frobenius ≫ (factorizationFrobeniusIso left right).hom =
      right.frobenius := by
  have leftPreDegree := left.preStep_type.1
  have rightPreDegree := right.preStep_type.1
  have leftPullDegree := (isPullback_iff_isLinear left.pullback).1 left.pullback_type
  have rightPullDegree := (isPullback_iff_isLinear right.pullback).1 right.pullback_type
  change left.preStep.frobeniusDegree = 1 at leftPreDegree
  change right.preStep.frobeniusDegree = 1 at rightPreDegree
  change left.pullback.frobeniusDegree = 1 at leftPullDegree
  change right.pullback.frobeniusDegree = 1 at rightPullDegree
  have degreeEquality : left.frobenius.frobeniusDegree =
      right.frobenius.frobeniusDegree := by
    have projected := congrArg P.frobeniusDegree
      (left.composite.trans right.composite.symm)
    rw [P.frobeniusDegree_comp, P.frobeniusDegree_comp,
      P.frobeniusDegree_comp, P.frobeniusDegree_comp] at projected
    simpa [leftPreDegree, rightPreDegree, leftPullDegree, rightPullDegree] using projected
  have leftBaseIsIso : IsIso left.frobenius.base :=
    (isOfFrobeniusType_iff_isBaseIso left.frobenius).1 left.frobenius_type
  letI : IsIso left.frobenius.base := leftBaseIsIso
  apply BirationalHom.ext
  · change left.frobenius.frobeniusDegree * 1 = right.frobenius.frobeniusDegree
    simpa using degreeEquality
  · change left.frobenius.base ≫
        (inv left.frobenius.base ≫ right.frobenius.base) = right.frobenius.base
    simp
  · change data.rationalFunctions.pullback left.frobenius.base
          (data.rationalFunctions.pullback (inv left.frobenius.base)
            (right.frobenius.rationalFunction - left.frobenius.rationalFunction)) +
          1 • left.frobenius.rationalFunction = right.frobenius.rationalFunction
    rw [← AddMonoidHom.comp_apply, ← data.rationalFunctions.pullback_comp,
      IsIso.hom_inv_id, data.rationalFunctions.pullback_id]
    simp only [AddMonoidHom.id_apply, one_nsmul]
    abel

/-- The comparison of pre-step codomains in two factorizations. -/
def factorizationPreStepIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} (left right : P.FrobenioidFactorization arrow) :
    left.preStepCodomain ≅ right.preStepCodomain := by
  haveI : IsIso left.preStep := isIso_of_isPreStep left.preStep left.preStep_type
  haveI : IsIso right.preStep := isIso_of_isPreStep right.preStep right.preStep_type
  exact (asIso left.preStep).symm ≪≫
    factorizationFrobeniusIso left right ≪≫ asIso right.preStep

/-- Essential uniqueness in Definition 1.3(iv)(a). -/
def factorizationIso
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : BirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} (left right : P.FrobenioidFactorization arrow) :
    P.FrobenioidFactorizationIso left right where
  frobeniusCodomainIso := factorizationFrobeniusIso left right
  preStepCodomainIso := factorizationPreStepIso left right
  frobenius_square := factorization_frobenius_square left right
  preStep_square := by
    dsimp [factorizationPreStepIso]
    simp
  pullback_square := by
    haveI : IsIso left.preStep := isIso_of_isPreStep left.preStep left.preStep_type
    haveI : IsIso right.preStep := isIso_of_isPreStep right.preStep right.preStep_type
    letI : Epi left.frobenius := epi baseTotallyEpimorphic left.frobenius
    have tailEquality : left.preStep ≫ left.pullback =
        (factorizationFrobeniusIso left right).hom ≫
          right.preStep ≫ right.pullback := by
      apply (cancel_epi left.frobenius).mp
      calc
        left.frobenius ≫ (left.preStep ≫ left.pullback) =
            left.frobenius ≫ left.preStep ≫ left.pullback := by simp
        _ = arrow := left.composite
        _ = right.frobenius ≫ right.preStep ≫ right.pullback :=
          right.composite.symm
        _ = (left.frobenius ≫
              (factorizationFrobeniusIso left right).hom) ≫
              right.preStep ≫ right.pullback := by
            rw [factorization_frobenius_square left right]
        _ = left.frobenius ≫
              ((factorizationFrobeniusIso left right).hom ≫
                right.preStep ≫ right.pullback) := by simp
    calc
      (factorizationPreStepIso left right).inv ≫ left.pullback =
          inv right.preStep ≫ (factorizationFrobeniusIso left right).inv ≫
            left.preStep ≫ left.pullback := by
              simp only [factorizationPreStepIso, Iso.trans_inv, Iso.symm_inv]
              change ((inv right.preStep ≫
                (factorizationFrobeniusIso left right).inv) ≫
                  left.preStep) ≫ left.pullback = _
              simp only [Category.assoc]
      _ = inv right.preStep ≫ (factorizationFrobeniusIso left right).inv ≫
            (left.preStep ≫ left.pullback) := by simp
      _ = inv right.preStep ≫ (factorizationFrobeniusIso left right).inv ≫
            ((factorizationFrobeniusIso left right).hom ≫
              right.preStep ≫ right.pullback) := by rw [tailEquality]
      _ = right.pullback := by simp

theorem factorizationIso_unique
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : BirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} (left right : P.FrobenioidFactorization arrow)
    (first second : P.FrobenioidFactorizationIso left right) : first = second := by
  have firstIso : first.frobeniusCodomainIso = second.frobeniusCodomainIso := by
    apply Iso.ext
    letI : Epi left.frobenius := epi baseTotallyEpimorphic left.frobenius
    apply (cancel_epi left.frobenius).mp
    exact first.frobenius_square.trans second.frobenius_square.symm
  have secondIso : first.preStepCodomainIso = second.preStepCodomainIso := by
    apply Iso.ext
    haveI : IsIso left.preStep := isIso_of_isPreStep left.preStep left.preStep_type
    have firstSquare := first.preStep_square
    have secondSquare := second.preStep_square
    rw [← firstIso] at secondSquare
    apply (cancel_epi (first.frobeniusCodomainIso.inv ≫ left.preStep)).mp
    simpa only [Category.assoc] using firstSquare.trans secondSquare.symm
  cases first
  cases second
  cases firstIso
  cases secondIso
  rfl

/-- The identity-first factorization supplies both orders in Definition 1.3(v). -/
def preStepFactorization
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (preStep : P.IsPreStep arrow)
    (coAngularFirst : Bool) : P.PreStepFactorization arrow coAngularFirst where
  midpoint := source
  first := 𝟙 source
  second := arrow
  first_preStep := by rw [← isIso_iff_isPreStep]; infer_instance
  second_preStep := preStep
  first_kind := by cases coAngularFirst <;> simp [isCoAngular, isIsometric]
  second_kind := by cases coAngularFirst <;> simp [isCoAngular, isIsometric]
  composite := by simp

/-- Comparison between two ordered pre-step factorizations. -/
def preStepFactorizationIso
    {source target : BirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} {coAngularFirst : Bool}
    (left right : P.PreStepFactorization arrow coAngularFirst) :
    P.PreStepFactorizationIso left right := by
  haveI : IsIso left.first := isIso_of_isPreStep left.first left.first_preStep
  haveI : IsIso right.first := isIso_of_isPreStep right.first right.first_preStep
  let comparison := (asIso left.first).symm ≪≫ asIso right.first
  refine
    { midpointIso := comparison
      first_square := by simp [comparison]
      second_square := ?_ }
  apply (cancel_epi right.first).mp
  rw [← Category.assoc]
  simp [comparison, left.composite, right.composite]

theorem preStepFactorizationIso_unique
    {source target : BirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} {coAngularFirst : Bool}
    (left right : P.PreStepFactorization arrow coAngularFirst)
    (first second : P.PreStepFactorizationIso left right) : first = second := by
  have isoEquality : first.midpointIso = second.midpointIso := by
    apply Iso.ext
    haveI : IsIso left.first := isIso_of_isPreStep left.first left.first_preStep
    apply (cancel_epi left.first).mp
    exact first.first_square.trans second.first_square.symm
  cases first
  cases second
  cases isoEquality
  rfl

theorem baseIdentityAutomorphism_ext
    {object : BirationalObject (Phi := Phi) (data := data)}
    {left right : P.BaseIdentityAutomorphism object}
    (isoEquality : left.iso = right.iso) : left = right := by
  cases left
  cases right
  cases isoEquality
  rfl

theorem faithfulUpToUnits
    {source target : BirationalObject (Phi := Phi) (data := data)}
    (first second : source ⟶ target) (baseEquality : first.base = second.base)
    (firstPreStep : P.IsPreStep first) (secondPreStep : P.IsPreStep second) :
    ∃! alpha : P.BaseIdentityAutomorphism target,
      second ≫ alpha.iso.hom = first := by
  haveI : IsIso first := isIso_of_isPreStep first firstPreStep
  haveI : IsIso second := isIso_of_isPreStep second secondPreStep
  have firstBaseIsIso := firstPreStep.2
  have secondBaseIsIso := secondPreStep.2
  change IsIso first.base at firstBaseIsIso
  change IsIso second.base at secondBaseIsIso
  letI : IsIso first.base := firstBaseIsIso
  letI : IsIso second.base := secondBaseIsIso
  let alpha : P.BaseIdentityAutomorphism target :=
    { iso := (asIso second).symm ≪≫ asIso first
      baseIdentity := by
        change P.base.map (inv second ≫ first) = 𝟙 _
        rw [P.base.map_comp]
        change (inv second).base ≫ first.base = 𝟙 _
        rw [baseEquality]
        simpa only [Category.comp_id] using
          congrArg BirationalHom.base
            (IsIso.inv_hom_id_assoc second (𝟙 target)) }
  have alphaComp : second ≫ alpha.iso.hom = first := by simp [alpha]
  refine ⟨alpha, alphaComp, ?_⟩
  intro candidate equality
  have isoEquality : candidate.iso = alpha.iso := by
    apply Iso.ext
    apply (cancel_epi second).mp
    exact equality.trans alphaComp.symm
  exact baseIdentityAutomorphism_ext isoEquality

/-- Since every target object is isotropic, its identity is its hull. -/
def isotropicHull
    (object : BirationalObject (Phi := Phi) (data := data)) :
    P.IsotropicHull object where
  hull := object
  hom := 𝟙 object
  preStep := by rw [← isIso_iff_isPreStep]; infer_instance
  isometric := isIsometric _
  isotropic := isIsotropic object
  lift := by
    intro target arrow _
    refine ⟨arrow, by simp, ?_⟩
    intro candidate equality
    simpa using equality

/-- The concrete birational target satisfies every axiom of Definition 1.3. -/
def frobenioidAxioms
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f) :
    (preFrobenioid (Phi := Phi) (data := data)).FrobenioidAxioms where
  baseRepresented := baseRepresented
  commonPreSteps left right baseIso := ⟨commonPreSteps left right baseIso⟩
  pullbackBaseSlices := pullbackBaseSlices
  frobeniusDegree := frobeniusDegreeWitness baseTotallyEpimorphic
  coAngular_comp first second _ _ := isCoAngular (first ≫ second)
  coAngular_parallelToCoAngularPreStep _ second _ _ := isCoAngular second
  unitTransport arrow preStep _ := unitTransport arrow preStep
  unitTransport_unique arrow _ _ := unitTransport_unique baseTotallyEpimorphic arrow
  unitTransport_dependsOnlyOnBase left right leftPre _ rightPre _ equality :=
    unitTransport_dependsOnlyOnBase left right leftPre rightPre equality
  outgoingDivisorRepresentative := outgoingDivisorRepresentative
  outgoingDivisorOrderFullyFaithful := outgoingDivisorOrderFullyFaithful
  outgoingDivisorRepresentative_unique := outgoingDivisorRepresentative_unique
  incomingDivisor arrow _ _ := incomingDivisor arrow
  incomingDivisorRepresentative := incomingDivisorRepresentative
  incomingDivisorOrderFullyFaithful := incomingDivisorOrderFullyFaithful
  incomingDivisorRepresentative_unique := incomingDivisorRepresentative_unique
  factorization arrow := ⟨factorization arrow⟩
  pullback_linear_lbInvertible arrow pullback :=
    ⟨(isPullback_iff_isLinear arrow).1 pullback, isLBInvertible arrow⟩
  factorizationIso := factorizationIso baseTotallyEpimorphic
  factorizationIso_unique := factorizationIso_unique baseTotallyEpimorphic
  preStep_mono arrow preStep := by
    haveI : IsIso arrow := isIso_of_isPreStep arrow preStep
    infer_instance
  preStep_coAngularThenIsometric arrow preStep :=
    ⟨preStepFactorization arrow preStep true⟩
  preStep_isometricThenCoAngular arrow preStep :=
    ⟨preStepFactorization arrow preStep false⟩
  preStepFactorizationIso := preStepFactorizationIso
  preStepFactorizationIso_unique := preStepFactorizationIso_unique
  faithfulUpToUnits first second baseEquality _ firstPre _ secondPre _ :=
    faithfulUpToUnits first second baseEquality firstPre secondPre
  isotropicHull object := ⟨isotropicHull object⟩
  isotropic_closedUnderTargets arrow _ := isIsotropic _

/-- The concrete birational model as a full Frobenioid presentation. -/
def frobenioidPresentation [IsConnected D]
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation where
  carrier := Cat.of (BirationalObject (Phi := Phi) (data := data))
  baseCategory := Cat.of D
  isFSM := IsFSM
  preFrobenioid := preFrobenioid (Phi := Phi) (data := data)
  carrierConnected := isConnected
  baseConnected := (inferInstance : IsConnected D)
  carrierTotallyEpimorphic := epi baseTotallyEpimorphic
  baseTotallyEpimorphic := baseTotallyEpimorphic
  axioms := frobenioidAxioms baseTotallyEpimorphic

end

end Iut.SourceModelFrobenioid.BirationalObject
