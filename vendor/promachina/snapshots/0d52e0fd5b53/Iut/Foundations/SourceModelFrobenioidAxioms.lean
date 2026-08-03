/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidPreStepFactorization

/-!
# The complete Definition 1.3 axiom package for the source model Frobenioid

This file proves Frobenioids I, Definition 1.3(vi), by constructing the unique
target-side unit that corrects two base- and divisor-equivalent co-angular
pre-steps.  It then assembles clauses (i)-(vii) into a single
`FrobenioidAxioms` value for the model category of Theorem 5.2.
-/

open CategoryTheory
namespace Iut.SourceModelFrobenioid.Carrier
universe u
noncomputable section
variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- The target-side unit correcting two equivalent model pre-steps. -/
def faithfulUnitRationalFunction
    {source target : Carrier Phi data} (first second : source ⟶ target)
    (secondPreStep : (preFrobenioid Phi data).IsPreStep second) :
    data.rationalFunctions.obj (Object.base target) :=
  letI : IsIso second.base := secondPreStep.2
  data.rationalFunctions.pullback (inv second.base)
    (first.rationalFunction - second.rationalFunction)

theorem faithfulUnitRationalFunction_divisor_eq_zero
    {source target : Carrier Phi data} (first second : source ⟶ target)
    (baseEquality : first.base = second.base)
    (divisorEquality : first.divisor = second.divisor)
    (firstPreStep : (preFrobenioid Phi data).IsPreStep first)
    (secondPreStep : (preFrobenioid Phi data).IsPreStep second) :
    data.divisor (Object.base target)
      (faithfulUnitRationalFunction first second secondPreStep) = 0 := by
  have baseIsIso := secondPreStep.2
  change IsIso second.base at baseIsIso
  letI : IsIso second.base := baseIsIso
  have firstLinear := firstPreStep.1
  change first.frobeniusDegree = 1 at firstLinear
  have secondLinear := secondPreStep.1
  change second.frobeniusDegree = 1 at secondLinear
  have firstBalance := first.balance
  have secondBalance := second.balance
  rw [firstLinear] at firstBalance
  rw [secondLinear] at secondBalance
  have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
  rw [degreeOne, one_nsmul] at firstBalance secondBalance
  rw [baseEquality, divisorEquality] at firstBalance
  have divisorValueEquality :
      data.divisor (Object.base source) first.rationalFunction =
        data.divisor (Object.base source) second.rationalFunction := by
    exact add_left_cancel (firstBalance.symm.trans secondBalance)
  have differenceDivisor :
      data.divisor (Object.base source)
          (first.rationalFunction - second.rationalFunction) = 0 := by
    rw [map_sub, divisorValueEquality, sub_self]
  unfold faithfulUnitRationalFunction
  change data.divisor (Object.base target)
      (data.rationalFunctions.pullback (inv second.base)
        (first.rationalFunction - second.rationalFunction)) = 0
  rw [data.divisor_natural, differenceDivisor, map_zero]

/-- The base-identity automorphism arrow supplied by Definition 1.3(vi). -/
def faithfulUnitHom
    {source target : Carrier Phi data} (first second : source ⟶ target)
    (baseEquality : first.base = second.base)
    (divisorEquality : first.divisor = second.divisor)
    (firstPreStep : (preFrobenioid Phi data).IsPreStep first)
    (secondPreStep : (preFrobenioid Phi data).IsPreStep second) :
    target ⟶ target where
  frobeniusDegree := 1
  base := 𝟙 (Object.base target)
  divisor := 0
  rationalFunction := faithfulUnitRationalFunction first second secondPreStep
  balance := by
    have rationalDivisor := faithfulUnitRationalFunction_divisor_eq_zero
      first second baseEquality divisorEquality firstPreStep secondPreStep
    change (1 : ℕ) • target.divisorClass +
          Algebra.GrothendieckAddGroup.of 0 =
        gpPullback Phi (𝟙 (Object.base target)) target.divisorClass +
          data.divisor (Object.base target)
            (faithfulUnitRationalFunction first second secondPreStep)
    rw [one_nsmul, gpPullback_id, rationalDivisor]
    simp only [AddMonoidHom.id_apply, add_zero]
    exact (congrArg (fun value ↦ target.divisorClass + value)
      (AddMonoidHom.map_zero Algebra.GrothendieckAddGroup.of)).trans
        (add_zero target.divisorClass)

theorem faithfulUnitHom_comp
    {source target : Carrier Phi data} (first second : source ⟶ target)
    (baseEquality : first.base = second.base)
    (divisorEquality : first.divisor = second.divisor)
    (firstPreStep : (preFrobenioid Phi data).IsPreStep first)
    (secondPreStep : (preFrobenioid Phi data).IsPreStep second) :
    second ≫ faithfulUnitHom first second baseEquality divisorEquality
        firstPreStep secondPreStep = first := by
  have baseIsIso := secondPreStep.2
  change IsIso second.base at baseIsIso
  letI : IsIso second.base := baseIsIso
  apply Hom.ext
  · rw [comp_frobeniusDegree]
    dsimp only [faithfulUnitHom]
    have firstLinear := firstPreStep.1
    change first.frobeniusDegree = 1 at firstLinear
    have secondLinear := secondPreStep.1
    change second.frobeniusDegree = 1 at secondLinear
    rw [firstLinear, secondLinear]
    exact one_mul 1
  · rw [comp_base]
    dsimp only [faithfulUnitHom]
    rw [Category.comp_id]
    exact baseEquality.symm
  · rw [comp_divisor]
    dsimp only [faithfulUnitHom]
    rw [map_zero, zero_add]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    exact divisorEquality.symm
  · rw [comp_rationalFunction]
    dsimp only [faithfulUnitHom, faithfulUnitRationalFunction]
    rw [← AddMonoidHom.comp_apply,
      ← data.rationalFunctions.pullback_comp,
      IsIso.hom_inv_id, data.rationalFunctions.pullback_id]
    simp only [AddMonoidHom.id_apply]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    abel

/-- The actual target-side base-identity automorphism. -/
def faithfulUnit
    {source target : Carrier Phi data} (first second : source ⟶ target)
    (baseEquality : first.base = second.base)
    (divisorEquality : first.divisor = second.divisor)
    (firstPreStep : (preFrobenioid Phi data).IsPreStep first)
    (secondPreStep : (preFrobenioid Phi data).IsPreStep second) :
    (preFrobenioid Phi data).BaseIdentityAutomorphism target := by
  let hom := faithfulUnitHom first second baseEquality divisorEquality
    firstPreStep secondPreStep
  have homPreStep : (preFrobenioid Phi data).IsPreStep hom := by
    constructor
    · rfl
    · change IsIso (𝟙 (Object.base target))
      infer_instance
  have homIsometric : (preFrobenioid Phi data).IsIsometric hom := rfl
  letI : IsIso hom := isIso_of_preStep_isometric Phi data hom
    homPreStep homIsometric
  exact
    { iso := asIso hom
      baseIdentity := rfl }

theorem baseIdentityAutomorphism_ext
    {object : Carrier Phi data}
    {left right : (preFrobenioid Phi data).BaseIdentityAutomorphism object}
    (iso : left.iso = right.iso) : left = right := by
  cases left
  cases right
  cases iso
  rfl

/-- Definition 1.3(vi), including uniqueness, for the model category. -/
theorem faithfulUpToUnits
    {source target : Carrier Phi data} (first second : source ⟶ target)
    (baseEquality : first.base = second.base)
    (divisorEquality : first.divisor = second.divisor)
    (firstPreStep : (preFrobenioid Phi data).IsPreStep first)
    (_firstCoAngular : (preFrobenioid Phi data).IsCoAngular first)
    (secondPreStep : (preFrobenioid Phi data).IsPreStep second)
    (_secondCoAngular : (preFrobenioid Phi data).IsCoAngular second) :
    ∃! alpha : (preFrobenioid Phi data).BaseIdentityAutomorphism target,
      second ≫ alpha.iso.hom = first := by
  let alpha := faithfulUnit first second baseEquality divisorEquality
    firstPreStep secondPreStep
  refine ⟨alpha, faithfulUnitHom_comp first second baseEquality
    divisorEquality firstPreStep secondPreStep, ?_⟩
  intro other otherComp
  apply baseIdentityAutomorphism_ext
  apply Iso.ext
  have secondBaseIsIso := secondPreStep.2
  change IsIso second.base at secondBaseIsIso
  letI : Epi second := epi_of_baseIsIso second secondBaseIsIso
  apply (cancel_epi second).mp
  exact otherComp.trans (faithfulUnitHom_comp first second baseEquality
    divisorEquality firstPreStep secondPreStep).symm

/-- The model category satisfies every axiom group of Definition 1.3. -/
def frobenioidAxioms
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f) :
    (preFrobenioid Phi data).FrobenioidAxioms where
  baseRepresented := baseRepresented Phi data
  commonPreSteps := commonPreSteps Phi data
  pullbackBaseSlices := pullbackBaseSlices Phi data
  frobeniusDegree := frobeniusDegreeWitness Phi data baseTotallyEpimorphic
  coAngular_comp := coAngular_comp Phi data
  coAngular_parallelToCoAngularPreStep := parallelToCoAngularPreStep Phi data
  unitTransport f preStep _ := unitTransport Phi data f preStep
  unitTransport_unique f _ _ left right :=
    unitTransport_unique Phi data f left right
  unitTransport_dependsOnlyOnBase f g hfPreStep _ hgPreStep _ equality :=
    unitTransport_dependsOnlyOnBase Phi data f g hfPreStep hgPreStep equality
  outgoingDivisorRepresentative := outgoingDivisorRepresentative
  outgoingDivisorOrderFullyFaithful := outgoingDivisorOrderFullyFaithful
  outgoingDivisorRepresentative_unique := outgoingDivisorRepresentative_unique
  incomingDivisor f preStep _ := incomingDivisor f preStep
  incomingDivisorRepresentative := incomingDivisorRepresentative
  incomingDivisorOrderFullyFaithful := incomingDivisorOrderFullyFaithful
  incomingDivisorRepresentative_unique := incomingDivisorRepresentative_unique
  factorization f := ⟨factorization f⟩
  pullback_linear_lbInvertible := pullback_linear_lbInvertible
  factorizationIso := factorizationIso baseTotallyEpimorphic
  factorizationIso_unique := factorizationIso_unique baseTotallyEpimorphic
  preStep_mono := preStep_mono
  preStep_coAngularThenIsometric f preStep :=
    ⟨preStep_coAngularThenIsometric f preStep⟩
  preStep_isometricThenCoAngular f preStep :=
    ⟨preStep_isometricThenCoAngular f preStep⟩
  preStepFactorizationIso := preStepFactorizationIso
  preStepFactorizationIso_unique :=
    preStepFactorizationIso_unique baseTotallyEpimorphic
  faithfulUpToUnits := faithfulUpToUnits
  isotropicHull A := ⟨isotropicHull Phi data A⟩
  isotropic_closedUnderTargets := isotropic_closedUnderTargets Phi data

end
end Iut.SourceModelFrobenioid.Carrier
