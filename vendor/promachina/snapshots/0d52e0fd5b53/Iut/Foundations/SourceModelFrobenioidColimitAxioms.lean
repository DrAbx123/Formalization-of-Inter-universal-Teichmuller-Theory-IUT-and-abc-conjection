/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidBirationalAxioms

/-!
# Definition 1.3 for the Hom-colimit birationalization

This file transports the explicit seven-axiom construction for the concrete
birational model to the actual filtered Hom-colimit category of Frobenioids I,
Proposition 4.4.  All transported arrows are obtained from the proved fully
faithful comparison, and equations are reflected through its injective Hom map.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid.Carrier.ColimitBirationalObject

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

private abbrev P := preFrobenioid (Phi := Phi) (data := data)
private abbrev Q := BirationalObject.preFrobenioid
  (Phi := Phi) (data := data)

private abbrev comparison := comparisonFunctor (Phi := Phi) (data := data)
private abbrev fullyFaithful :=
  comparisonFunctor_fullyFaithful (Phi := Phi) (data := data)

/-- Lift a concrete arrow through the fully faithful comparison. -/
def liftHom
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : comparison.obj source ⟶ comparison.obj target) : source ⟶ target :=
  fullyFaithful.preimage arrow

@[simp]
theorem comparison_map_liftHom
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : comparison.obj source ⟶ comparison.obj target) :
    comparison.map (liftHom arrow) = arrow :=
  fullyFaithful.map_preimage arrow

/-- Lift a concrete isomorphism through the fully faithful comparison. -/
def liftIso
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (iso : comparison.obj source ≅ comparison.obj target) : source ≅ target where
  hom := liftHom iso.hom
  inv := liftHom iso.inv
  hom_inv_id := by
    apply fullyFaithful.map_injective
    rw [comparison.map_comp, comparison_map_liftHom,
      comparison_map_liftHom, iso.hom_inv_id, comparison.map_id]
  inv_hom_id := by
    apply fullyFaithful.map_injective
    rw [comparison.map_comp, comparison_map_liftHom,
      comparison_map_liftHom, iso.inv_hom_id, comparison.map_id]

@[simp]
theorem comparison_map_liftIso_hom
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (iso : comparison.obj source ≅ comparison.obj target) :
    comparison.map (liftIso iso).hom = iso.hom :=
  comparison_map_liftHom iso.hom

@[simp]
theorem comparison_map_liftIso_inv
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (iso : comparison.obj source ≅ comparison.obj target) :
    comparison.map (liftIso iso).inv = iso.inv :=
  comparison_map_liftHom iso.inv

/-- The Hom-colimit object over a prescribed base object. -/
def zeroObject (base : D) :
    ColimitBirationalObject (Phi := Phi) (data := data) :=
  ⟨Carrier.zeroObject Phi data base⟩

/-- The lifted canonical Frobenius endomorphism. -/
def frobeniusHom
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (degree : ℕ+) : object ⟶ object :=
  liftHom (BirationalObject.frobeniusHom (comparison.obj object) degree)

@[simp]
theorem comparison_map_frobeniusHom
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (degree : ℕ+) :
    comparison.map (frobeniusHom object degree) =
      BirationalObject.frobeniusHom (comparison.obj object) degree :=
  comparison_map_liftHom _

/-- Every Hom-colimit object is Frobenius-trivial. -/
def frobeniusTrivialization
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    P.FrobeniusTrivialization object where
  lift := frobeniusHom object
  map_one := by
    apply fullyFaithful.map_injective
    rw [comparison_map_frobeniusHom, comparison.map_id]
    exact (BirationalObject.frobeniusTrivialization
      (comparison.obj object)).map_one
  map_mul m n := by
    apply fullyFaithful.map_injective
    rw [comparison_map_frobeniusHom, comparison.map_comp,
      comparison_map_frobeniusHom, comparison_map_frobeniusHom]
    exact (BirationalObject.frobeniusTrivialization
      (comparison.obj object)).map_mul m n
  degree_section n := by
    change (comparison.map (frobeniusHom object n)).frobeniusDegree = n
    rw [comparison_map_frobeniusHom]
    rfl
  base_identity n := by
    change (comparison.map (frobeniusHom object n)).base = 𝟙 _
    rw [comparison_map_frobeniusHom]
    rfl
  of_frobenius_type n := by
    apply (isOfFrobeniusType_iff_isBaseIso _).2
    change IsIso (comparison.map (frobeniusHom object n)).base
    rw [comparison_map_frobeniusHom]
    change IsIso (𝟙 _)
    infer_instance

/-- Definition 1.3(i)(a) for the actual Hom-colimit target. -/
theorem baseRepresented (base : D) :
    ∃ object : ColimitBirationalObject (Phi := Phi) (data := data),
      P.IsFrobeniusTrivial object ∧ Nonempty (P.base.obj object ≅ base) :=
  ⟨zeroObject base, ⟨frobeniusTrivialization (zeroObject base)⟩,
    ⟨Iso.refl base⟩⟩

/-- A degree-one lift of a concrete arrow over a prescribed base isomorphism. -/
def commonPreStepHom
    (left right : ColimitBirationalObject (Phi := Phi) (data := data))
    (baseIso : P.base.obj left ≅ P.base.obj right) : left ⟶ right :=
  liftHom (source := left) (target := right)
    { frobeniusDegree := 1
      base := baseIso.hom
      rationalFunction := 0 }

/-- Definition 1.3(i)(b) for the Hom-colimit target. -/
def commonPreSteps
    (left right : ColimitBirationalObject (Phi := Phi) (data := data))
    (baseIso : P.base.obj left ≅ P.base.obj right) :
    P.CommonPreStepWitness left right baseIso where
  midpoint := left
  toLeft := 𝟙 left
  toRight := commonPreStepHom left right baseIso
  toLeft_preStep := by rw [← isIso_iff_isPreStep]; infer_instance
  toRight_preStep := by
    rw [← isIso_iff_isPreStep]
    haveI : IsIso (comparison.map (commonPreStepHom left right baseIso)) := by
      change IsIso (comparison.map (liftHom
        { frobeniusDegree := 1
          base := baseIso.hom
          rationalFunction := 0 }))
      rw [comparison_map_liftHom]
      exact (BirationalObject.isoOfLinearBaseIso _ rfl inferInstance).isIso_hom
    exact fullyFaithful.isIso_of_isIso_map _
  leftBaseInverse := 𝟙 _
  leftBaseInverse_hom := by
    rw [P.base.map_id]
    simp
  hom_leftBaseInverse := by
    rw [P.base.map_id]
    simp
  comparison := by
    change 𝟙 _ ≫ (comparison.map (commonPreStepHom left right baseIso)).base =
      baseIso.hom
    rw [Category.id_comp]
    change (comparison.map (liftHom
      { frobeniusDegree := 1
        base := baseIso.hom
        rationalFunction := 0 })).base = baseIso.hom
    rw [comparison_map_liftHom]

/-- A pullback arrow realizing an arbitrary object of the base slice. -/
def baseSliceLift
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (value : P.BaseSliceObject object) :
    PreFrobenioid.PullbackSliceObject object where
  source := zeroObject value.source
  hom := liftHom (source := zeroObject value.source) (target := object)
    { frobeniusDegree := 1
      base := value.hom
      rationalFunction := 0 }

theorem baseSliceLift_isPullback
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (value : P.BaseSliceObject object) :
    P.IsPullback (baseSliceLift object value).hom := by
  apply (isPullback_iff_isLinear _).2
  change (comparison.map (liftHom (source := zeroObject value.source)
    (target := object)
    { frobeniusDegree := 1
      base := value.hom
      rationalFunction := 0 })).frobeniusDegree = 1
  rw [comparison_map_liftHom]

/-- Lift a base-slice map by the representable pullback universal property. -/
def pullbackSlicePreimage
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (left right : PreFrobenioid.PullbackSliceObject object)
    (_leftPullback : P.IsPullback left.hom)
    (rightPullback : P.IsPullback right.hom)
    (value : P.BaseSliceHom (left.toBase P) (right.toBase P)) :
    PreFrobenioid.PullbackSliceHom left right := by
  let comparisonTarget : P.PullbackComparisonTarget right.hom left.source :=
    { toCodomain := left.hom
      toBaseDomain := value.hom
      commutes := value.commutes.symm }
  let lift := Classical.choose ((rightPullback left.source).2 comparisonTarget)
  have liftComparison :=
    Classical.choose_spec ((rightPullback left.source).2 comparisonTarget)
  exact
    { hom := lift
      commutes := congrArg
        PreFrobenioid.PullbackComparisonTarget.toCodomain liftComparison }

theorem baseSliceHom_ext
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    {left right : P.BaseSliceObject object}
    {first second : P.BaseSliceHom left right}
    (homEquality : first.hom = second.hom) : first = second := by
  cases first
  cases second
  cases homEquality
  rfl

theorem pullbackSlicePreimage_toBase
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (left right : PreFrobenioid.PullbackSliceObject object)
    (leftPullback : P.IsPullback left.hom)
    (rightPullback : P.IsPullback right.hom)
    (value : P.BaseSliceHom (left.toBase P) (right.toBase P)) :
    (pullbackSlicePreimage object left right leftPullback rightPullback value).toBase P =
      value := by
  apply baseSliceHom_ext
  exact congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain
    (Classical.choose_spec ((rightPullback left.source).2
      { toCodomain := left.hom
        toBaseDomain := value.hom
        commutes := value.commutes.symm }))

theorem pullbackSliceProjection_bijective
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
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
        have baseEquality : P.base.map first = P.base.map second :=
          congrArg PreFrobenioid.BaseSliceHom.hom equality
        have compositeEquality : first ≫ right.hom = second ≫ right.hom :=
          firstCommutes.trans secondCommutes.symm
        apply (rightPullback left.source).1
        apply pullbackComparisonTarget_ext
        · exact compositeEquality
        · exact baseEquality
  · intro value
    exact ⟨pullbackSlicePreimage object left right leftPullback rightPullback value,
      pullbackSlicePreimage_toBase object left right leftPullback rightPullback value⟩

/-- Definition 1.3(i)(c) for the actual Hom-colimit target. -/
def pullbackBaseSlices
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    P.PullbackBaseSliceEquivalence object where
  essentiallySurjective value :=
    ⟨baseSliceLift object value, baseSliceLift_isPullback object value,
      ⟨{
        iso := Iso.refl value.source
        hom_commutes := by
          change 𝟙 value.source ≫ value.hom =
            (comparison.map (baseSliceLift object value).hom).base
          change 𝟙 value.source ≫ value.hom =
            (comparison.map (liftHom (source := zeroObject value.source)
              (target := object)
              { frobeniusDegree := 1
                base := value.hom
                rationalFunction := 0 })).base
          rw [comparison_map_liftHom]
          simp
      }⟩⟩
  fullyFaithful left right leftPullback rightPullback :=
    pullbackSliceProjection_bijective object left right leftPullback rightPullback

/-- Definition 1.3(ii)'s degree witness on the actual Hom colimit. -/
def frobeniusDegreeWitness
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (degree : ℕ+) : P.FrobeniusDegreeWitness object degree where
  codomain := object
  hom := frobeniusHom object degree
  ofFrobeniusType := (frobeniusTrivialization object).of_frobenius_type degree
  degree := (frobeniusTrivialization object).degree_section degree
  essentiallyUnique := by
    intro target arrow arrowType arrowDegree
    have concreteType : Q.IsOfFrobeniusType (comparison.map arrow) := by
      apply (BirationalObject.isOfFrobeniusType_iff_isBaseIso _).2
      exact arrowType.2
    have concreteDegree : Q.frobeniusDegree (comparison.map arrow) = degree :=
      arrowDegree
    obtain ⟨concreteIso, concreteComp, concreteUnique⟩ :=
      (BirationalObject.frobeniusDegreeWitness baseTotallyEpimorphic
        (comparison.obj object) degree).essentiallyUnique
          (comparison.map arrow) concreteType concreteDegree
    let iso : object ≅ target := liftIso concreteIso
    refine ⟨iso, ?_, ?_⟩
    · apply fullyFaithful.map_injective
      rw [comparison.map_comp, comparison_map_frobeniusHom,
        comparison_map_liftIso_hom]
      exact concreteComp
    · intro candidate candidateComp
      apply Iso.ext
      apply fullyFaithful.map_injective
      have mappedCandidateComp :
          BirationalObject.frobeniusHom (comparison.obj object) degree ≫
              (comparison.mapIso candidate).hom = comparison.map arrow := by
        rw [← comparison_map_frobeniusHom]
        change comparison.map (frobeniusHom object degree) ≫
            comparison.map candidate.hom = comparison.map arrow
        rw [← comparison.map_comp, candidateComp]
      have isoEquality := concreteUnique (comparison.mapIso candidate)
        mappedCandidateComp
      change comparison.map candidate.hom = comparison.map iso.hom
      rw [show comparison.map iso.hom = concreteIso.hom from
        comparison_map_liftIso_hom concreteIso]
      exact congrArg Iso.hom isoEquality

/-- A colimit pre-step mapped to a concrete pre-step. -/
def mappedPreStep
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (preStep : P.IsPreStep arrow) :
    Q.IsPreStep (comparison.map arrow) := by
  rw [← BirationalObject.isIso_iff_isPreStep]
  haveI : IsIso arrow := (isIso_iff_isPreStep arrow).2 preStep
  infer_instance

/-- Transport of `O^bullet` induced from the concrete comparison target. -/
def unitTransport
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (preStep : P.IsPreStep arrow) :
    P.CoAngularUnitTransport arrow where
  transport :=
    (linearBaseIdentityEndomorphismEquiv (Phi := Phi) (data := data) source).trans
      ((BirationalObject.unitTransport (comparison.map arrow)
        (mappedPreStep arrow preStep)).transport.trans
        (linearBaseIdentityEndomorphismEquiv
          (Phi := Phi) (data := data) target).symm)
  conjugates alpha := by
    apply fullyFaithful.map_injective
    rw [comparison.map_comp, comparison.map_comp]
    let beta := (BirationalObject.unitTransport (comparison.map arrow)
      (mappedPreStep arrow preStep)).transport
        ((linearBaseIdentityEndomorphismEquiv
          (Phi := Phi) (data := data) source) alpha)
    have targetMap := congrArg
      (fun value : Q.LinearBaseIdentityEndomorphism (comparison.obj target) ↦
        value.hom)
      ((linearBaseIdentityEndomorphismEquiv
        (Phi := Phi) (data := data) target).apply_symm_apply beta)
    change comparison.map
        ((linearBaseIdentityEndomorphismEquiv
          (Phi := Phi) (data := data) target).symm beta).hom = beta.hom
      at targetMap
    change comparison.map alpha.hom ≫ comparison.map arrow =
      comparison.map arrow ≫ comparison.map
        ((linearBaseIdentityEndomorphismEquiv
          (Phi := Phi) (data := data) target).symm beta).hom
    rw [targetMap]
    exact (BirationalObject.unitTransport (comparison.map arrow)
      (mappedPreStep arrow preStep)).conjugates
        ((linearBaseIdentityEndomorphismEquiv
          (Phi := Phi) (data := data) source) alpha)

theorem unitTransport_comparison
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (preStep : P.IsPreStep arrow)
    (alpha : P.LinearBaseIdentityEndomorphism source) :
    (linearBaseIdentityEndomorphismEquiv (Phi := Phi) (data := data) target)
        ((unitTransport arrow preStep).transport alpha) =
      (BirationalObject.unitTransport (comparison.map arrow)
        (mappedPreStep arrow preStep)).transport
        ((linearBaseIdentityEndomorphismEquiv
          (Phi := Phi) (data := data) source) alpha) := by
  change (linearBaseIdentityEndomorphismEquiv (Phi := Phi) (data := data) target)
      ((linearBaseIdentityEndomorphismEquiv
        (Phi := Phi) (data := data) target).symm
        ((BirationalObject.unitTransport (comparison.map arrow)
          (mappedPreStep arrow preStep)).transport
          ((linearBaseIdentityEndomorphismEquiv
            (Phi := Phi) (data := data) source) alpha))) = _
  exact (linearBaseIdentityEndomorphismEquiv
    (Phi := Phi) (data := data) target).apply_symm_apply _

theorem unitTransport_unique
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
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
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (left right : source ⟶ target)
    (leftPreStep : P.IsPreStep left) (rightPreStep : P.IsPreStep right)
    (baseEquality : P.base.map left = P.base.map right) :
    (unitTransport left leftPreStep).transport =
      (unitTransport right rightPreStep).transport := by
  apply MulEquiv.ext
  intro alpha
  apply (linearBaseIdentityEndomorphismEquiv
    (Phi := Phi) (data := data) target).injective
  rw [unitTransport_comparison, unitTransport_comparison]
  exact DFunLike.congr_fun
    (BirationalObject.unitTransport_dependsOnlyOnBase
      (comparison.map left) (comparison.map right)
      (mappedPreStep left leftPreStep)
      (mappedPreStep right rightPreStep)
      baseEquality) _

/-- The unique outgoing representative of the sole divisor in `0_D`. -/
def outgoingDivisorRepresentative
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (divisor : P.DivisorOrder object) :
    P.OutgoingCoAngularPreStep object divisor where
  target := object
  hom := 𝟙 object
  preStep := by rw [← isIso_iff_isPreStep]; infer_instance
  coAngular := isCoAngular _
  divisor_eq := by cases divisor; rfl

theorem outgoingDivisorOrderFullyFaithful
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    {leftDivisor rightDivisor : P.DivisorOrder object}
    (left : P.OutgoingCoAngularPreStep object leftDivisor)
    (right : P.OutgoingCoAngularPreStep object rightDivisor) :
    leftDivisor ≤ rightDivisor ↔
      ∃! arrow : left.target ⟶ right.target,
        left.hom ≫ arrow = right.hom := by
  constructor
  · intro _
    haveI : IsIso left.hom := (isIso_iff_isPreStep left.hom).2 left.preStep
    refine ⟨inv left.hom ≫ right.hom, by simp, ?_⟩
    intro arrow equality
    apply (cancel_epi left.hom).mp
    simpa using equality
  · intro _
    exact ⟨0, by cases leftDivisor; cases rightDivisor; rfl⟩

theorem outgoingDivisorRepresentative_unique
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    {divisor : P.DivisorOrder object}
    (left right : P.OutgoingCoAngularPreStep object divisor) :
    ∃! iso : left.target ≅ right.target,
      left.hom ≫ iso.hom = right.hom := by
  haveI : IsIso left.hom := (isIso_iff_isPreStep left.hom).2 left.preStep
  haveI : IsIso right.hom := (isIso_iff_isPreStep right.hom).2 right.preStep
  let iso := (asIso left.hom).symm ≪≫ asIso right.hom
  refine ⟨iso, by simp [iso], ?_⟩
  intro candidate equality
  apply Iso.ext
  apply (cancel_epi left.hom).mp
  simpa [iso] using equality

theorem incomingDivisor
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) :
    ∃! divisor : P.DivisorOrder target,
      P.divisorMonoid.pullback (P.base.map arrow) divisor = P.divisor arrow := by
  refine ⟨PUnit.unit, by rfl, ?_⟩
  intro value _
  cases value
  rfl

/-- The unique incoming representative of the sole divisor in `0_D`. -/
def incomingDivisorRepresentative
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (divisor : P.DivisorOrder object) :
    P.IncomingCoAngularPreStep object divisor where
  source := object
  hom := 𝟙 object
  preStep := by rw [← isIso_iff_isPreStep]; infer_instance
  coAngular := isCoAngular _
  pulledBack_divisor_eq := by cases divisor; rfl

theorem incomingDivisorOrderFullyFaithful
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    {leftDivisor rightDivisor : P.DivisorOrder object}
    (left : P.IncomingCoAngularPreStep object leftDivisor)
    (right : P.IncomingCoAngularPreStep object rightDivisor) :
    rightDivisor ≤ leftDivisor ↔
      ∃! arrow : left.source ⟶ right.source,
        arrow ≫ right.hom = left.hom := by
  constructor
  · intro _
    haveI : IsIso right.hom := (isIso_iff_isPreStep right.hom).2 right.preStep
    refine ⟨left.hom ≫ inv right.hom, by simp, ?_⟩
    intro arrow equality
    apply (cancel_mono right.hom).mp
    simpa using equality
  · intro _
    exact ⟨0, by cases leftDivisor; cases rightDivisor; rfl⟩

theorem incomingDivisorRepresentative_unique
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    {divisor : P.DivisorOrder object}
    (left right : P.IncomingCoAngularPreStep object divisor) :
    ∃! iso : left.source ≅ right.source,
      iso.hom ≫ right.hom = left.hom := by
  haveI : IsIso left.hom := (isIso_iff_isPreStep left.hom).2 left.preStep
  haveI : IsIso right.hom := (isIso_iff_isPreStep right.hom).2 right.preStep
  let iso := asIso left.hom ≪≫ (asIso right.hom).symm
  refine ⟨iso, by simp [iso], ?_⟩
  intro candidate equality
  apply Iso.ext
  apply (cancel_mono right.hom).mp
  simpa [iso] using equality

/-- Lift the concrete canonical three-stage factorization. -/
def factorization
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) : P.FrobenioidFactorization arrow := by
  let concrete := BirationalObject.factorization (comparison.map arrow)
  refine
    { frobeniusCodomain := source
      preStepCodomain := source
      frobenius := liftHom concrete.frobenius
      preStep := liftHom concrete.preStep
      pullback := liftHom concrete.pullback
      frobenius_type := ?_
      preStep_type := ?_
      pullback_type := ?_
      composite := ?_ }
  · apply (isOfFrobeniusType_iff_isBaseIso _).2
    change IsIso (comparison.map (liftHom concrete.frobenius)).base
    rw [comparison_map_liftHom]
    exact concrete.frobenius_type.2
  · rw [← isIso_iff_isPreStep]
    have concreteIsIso : IsIso concrete.preStep :=
      (BirationalObject.isIso_iff_isPreStep concrete.preStep).2
        concrete.preStep_type
    haveI : IsIso (comparison.map (liftHom concrete.preStep)) := by
      rw [comparison_map_liftHom]
      exact concreteIsIso
    exact fullyFaithful.isIso_of_isIso_map _
  · apply (isPullback_iff_isLinear _).2
    change (comparison.map (liftHom concrete.pullback)).frobeniusDegree = 1
    rw [comparison_map_liftHom]
    exact (BirationalObject.isPullback_iff_isLinear concrete.pullback).1
      concrete.pullback_type
  · apply fullyFaithful.map_injective
    rw [comparison.map_comp, comparison.map_comp,
      comparison_map_liftHom, comparison_map_liftHom,
      comparison_map_liftHom]
    exact concrete.composite

/-- Map an arbitrary Hom-colimit factorization to a concrete factorization. -/
def mappedFactorization
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} (value : P.FrobenioidFactorization arrow) :
    Q.FrobenioidFactorization (comparison.map arrow) where
  frobeniusCodomain := comparison.obj value.frobeniusCodomain
  preStepCodomain := comparison.obj value.preStepCodomain
  frobenius := comparison.map value.frobenius
  preStep := comparison.map value.preStep
  pullback := comparison.map value.pullback
  frobenius_type := by
    apply (BirationalObject.isOfFrobeniusType_iff_isBaseIso _).2
    exact value.frobenius_type.2
  preStep_type := mappedPreStep value.preStep value.preStep_type
  pullback_type := by
    apply (BirationalObject.isPullback_iff_isLinear _).2
    exact (isPullback_iff_isLinear value.pullback).1 value.pullback_type
  composite := by
    rw [← comparison.map_comp, ← comparison.map_comp, value.composite]

/-- Lift the concrete comparison of two arbitrary factorizations. -/
def factorizationIso
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} (left right : P.FrobenioidFactorization arrow) :
    P.FrobenioidFactorizationIso left right := by
  let concrete := BirationalObject.factorizationIso baseTotallyEpimorphic
    (mappedFactorization left) (mappedFactorization right)
  refine
    { frobeniusCodomainIso := liftIso concrete.frobeniusCodomainIso
      preStepCodomainIso := liftIso concrete.preStepCodomainIso
      frobenius_square := ?_
      preStep_square := ?_
      pullback_square := ?_ }
  · apply fullyFaithful.map_injective
    rw [comparison.map_comp, comparison_map_liftIso_hom]
    exact concrete.frobenius_square
  · apply fullyFaithful.map_injective
    rw [comparison.map_comp, comparison.map_comp,
      comparison_map_liftIso_inv, comparison_map_liftIso_hom]
    exact concrete.preStep_square
  · apply fullyFaithful.map_injective
    rw [comparison.map_comp, comparison_map_liftIso_inv]
    exact concrete.pullback_square

theorem factorizationIso_unique
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} (left right : P.FrobenioidFactorization arrow)
    (first second : P.FrobenioidFactorizationIso left right) : first = second := by
  have firstIso : first.frobeniusCodomainIso = second.frobeniusCodomainIso := by
    apply Iso.ext
    letI : Epi left.frobenius := epi baseTotallyEpimorphic left.frobenius
    apply (cancel_epi left.frobenius).mp
    exact first.frobenius_square.trans second.frobenius_square.symm
  have secondIso : first.preStepCodomainIso = second.preStepCodomainIso := by
    apply Iso.ext
    haveI : IsIso left.preStep :=
      (isIso_iff_isPreStep left.preStep).2 left.preStep_type
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
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
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
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} {coAngularFirst : Bool}
    (left right : P.PreStepFactorization arrow coAngularFirst) :
    P.PreStepFactorizationIso left right := by
  haveI : IsIso left.first := (isIso_iff_isPreStep left.first).2 left.first_preStep
  haveI : IsIso right.first := (isIso_iff_isPreStep right.first).2 right.first_preStep
  let comparisonIso := (asIso left.first).symm ≪≫ asIso right.first
  refine
    { midpointIso := comparisonIso
      first_square := by simp [comparisonIso]
      second_square := ?_ }
  apply (cancel_epi right.first).mp
  rw [← Category.assoc]
  simp [comparisonIso, left.composite, right.composite]

theorem preStepFactorizationIso_unique
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    {arrow : source ⟶ target} {coAngularFirst : Bool}
    (left right : P.PreStepFactorization arrow coAngularFirst)
    (first second : P.PreStepFactorizationIso left right) : first = second := by
  have isoEquality : first.midpointIso = second.midpointIso := by
    apply Iso.ext
    haveI : IsIso left.first := (isIso_iff_isPreStep left.first).2 left.first_preStep
    apply (cancel_epi left.first).mp
    exact first.first_square.trans second.first_square.symm
  cases first
  cases second
  cases isoEquality
  rfl

theorem baseIdentityAutomorphism_ext
    {object : ColimitBirationalObject (Phi := Phi) (data := data)}
    {left right : P.BaseIdentityAutomorphism object}
    (isoEquality : left.iso = right.iso) : left = right := by
  cases left
  cases right
  cases isoEquality
  rfl

/-- Definition 1.3(vi) for the actual Hom-colimit target. -/
theorem faithfulUpToUnits
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (first second : source ⟶ target)
    (baseEquality : P.base.map first = P.base.map second)
    (firstPreStep : P.IsPreStep first) (secondPreStep : P.IsPreStep second) :
    ∃! alpha : P.BaseIdentityAutomorphism target,
      second ≫ alpha.iso.hom = first := by
  haveI : IsIso first := (isIso_iff_isPreStep first).2 firstPreStep
  haveI : IsIso second := (isIso_iff_isPreStep second).2 secondPreStep
  let alpha : P.BaseIdentityAutomorphism target :=
    { iso := (asIso second).symm ≪≫ asIso first
      baseIdentity := by
        change P.base.map (inv second ≫ first) = 𝟙 _
        rw [P.base.map_comp, baseEquality]
        have projected := congrArg P.base.map
          (IsIso.inv_hom_id_assoc second (𝟙 target))
        simpa only [P.base.map_comp, P.base.map_id, Category.comp_id] using projected }
  have alphaComp : second ≫ alpha.iso.hom = first := by simp [alpha]
  refine ⟨alpha, alphaComp, ?_⟩
  intro candidate equality
  apply baseIdentityAutomorphism_ext
  apply Iso.ext
  apply (cancel_epi second).mp
  exact equality.trans alphaComp.symm

/-- Since every Hom-colimit object is isotropic, its identity is its hull. -/
def isotropicHull
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
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

/-- The actual filtered Hom-colimit satisfies every axiom of Definition 1.3. -/
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
    haveI : IsIso arrow := (isIso_iff_isPreStep arrow).2 preStep
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

/-- Proposition 4.4(ii)'s full Frobenioid presentation on the Hom colimit. -/
def frobenioidPresentation [IsConnected D]
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation where
  carrier := Cat.of (ColimitBirationalObject (Phi := Phi) (data := data))
  baseCategory := Cat.of D
  isFSM := IsFSM
  preFrobenioid := preFrobenioid (Phi := Phi) (data := data)
  carrierConnected := isConnected
  baseConnected := (inferInstance : IsConnected D)
  carrierTotallyEpimorphic := epi baseTotallyEpimorphic
  baseTotallyEpimorphic := baseTotallyEpimorphic
  axioms := frobenioidAxioms baseTotallyEpimorphic

end

end Iut.SourceModelFrobenioid.Carrier.ColimitBirationalObject
