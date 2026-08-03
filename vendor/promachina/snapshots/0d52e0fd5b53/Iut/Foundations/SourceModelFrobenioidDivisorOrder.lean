/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioid

/-!
# Divisor-order slice equivalences for the source model Frobenioid

This file implements Frobenioids I, Definition 1.3(iii)(d), for the model
category of Theorem 5.2.  Outgoing co-angular pre-steps realize the divisor
order, while incoming co-angular pre-steps realize its opposite.  Both
directions include explicit representatives, comparison arrows, full
faithfulness, and uniqueness up to a unique comparison isomorphism.
-/

open CategoryTheory
namespace Iut.SourceModelFrobenioid.Carrier
universe u
noncomputable section
variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- The target obtained by adding an effective divisor to a model object. -/
def outgoingDivisorTarget (object : Carrier Phi data)
    (divisor : (Phi.obj (Object.base object)).carrier) :
    Carrier Phi data where
  base := Object.base object
  divisorClass := object.divisorClass +
    Algebra.GrothendieckAddGroup.of divisor

def outgoingDivisorArrow (object : Carrier Phi data)
    (divisor : (Phi.obj (Object.base object)).carrier) :
    object ⟶ outgoingDivisorTarget object divisor where
  frobeniusDegree := 1
  base := 𝟙 (Object.base object)
  divisor := divisor
  rationalFunction := 0
  balance := by
    dsimp only [outgoingDivisorTarget]
    rw [gpPullback_id]
    simp only [map_zero, add_zero]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    rfl

def outgoingDivisorRepresentative (object : Carrier Phi data)
    (divisor : (preFrobenioid Phi data).DivisorOrder object) :
    (preFrobenioid Phi data).OutgoingCoAngularPreStep object divisor where
  target := outgoingDivisorTarget object divisor
  hom := outgoingDivisorArrow object divisor
  preStep := by
    constructor
    · rfl
    · change IsIso (𝟙 (Object.base object))
      infer_instance
  coAngular := isCoAngular Phi data (outgoingDivisorArrow object divisor)
  divisor_eq := rfl

theorem gpPullback_iso_injective {X Y : D} (f : X ⟶ Y)
    (baseIsIso : IsIso f) : Function.Injective (gpPullback Phi f) := by
  letI : IsIso f := baseIsIso
  intro left right equality
  have pulled := congrArg (gpPullback Phi (inv f)) equality
  simpa only [← AddMonoidHom.comp_apply, ← gpPullback_comp,
    IsIso.inv_hom_id, gpPullback_id, AddMonoidHom.id_apply] using pulled

def outgoingDivisorComparison
    {object : Carrier Phi data}
    {leftDivisor rightDivisor :
      (preFrobenioid Phi data).DivisorOrder object}
    (left : (preFrobenioid Phi data).OutgoingCoAngularPreStep
      object leftDivisor)
    (right : (preFrobenioid Phi data).OutgoingCoAngularPreStep
      object rightDivisor)
    (remainder : (preFrobenioid Phi data).DivisorOrder object)
    (divisorEquality : rightDivisor = leftDivisor + remainder) :
    left.target ⟶ right.target := by
  have leftBaseIsIso := left.preStep.2
  change IsIso left.hom.base at leftBaseIsIso
  letI : IsIso left.hom.base := leftBaseIsIso
  have rightBaseIsIso := right.preStep.2
  change IsIso right.hom.base at rightBaseIsIso
  letI : IsIso right.hom.base := rightBaseIsIso
  refine
    { frobeniusDegree := 1
      base := inv left.hom.base ≫ right.hom.base
      divisor := Phi.pullback (inv left.hom.base) remainder
      rationalFunction :=
        data.rationalFunctions.pullback (inv left.hom.base)
          (right.hom.rationalFunction - left.hom.rationalFunction)
      balance := ?_ }
  apply gpPullback_iso_injective left.hom.base leftBaseIsIso
  simp only [map_add]
  rw [gpPullback_of, data.divisor_natural]
  have divisorCancel :
      Phi.pullback left.hom.base
          (Phi.pullback (inv left.hom.base) remainder) = remainder := by
    rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
      IsIso.hom_inv_id, Phi.pullback_id]
    rfl
  have classTransport :
      gpPullback Phi left.hom.base
          (gpPullback Phi (inv left.hom.base ≫ right.hom.base)
            right.target.divisorClass) =
        gpPullback Phi right.hom.base right.target.divisorClass := by
    rw [← AddMonoidHom.comp_apply, ← gpPullback_comp,
      IsIso.hom_inv_id_assoc]
  have groupCancel
      (value : Algebra.GrothendieckAddGroup
        (Phi.obj (Object.base object)).carrier) :
      gpPullback Phi left.hom.base
          (gpPullback Phi (inv left.hom.base) value) = value := by
    rw [← AddMonoidHom.comp_apply, ← gpPullback_comp,
      IsIso.hom_inv_id, gpPullback_id]
    rfl
  rw [divisorCancel, classTransport, groupCancel]
  have leftLinear := left.preStep.1
  change left.hom.frobeniusDegree = 1 at leftLinear
  have leftDivisorEq := left.divisor_eq
  change left.hom.divisor = leftDivisor at leftDivisorEq
  have leftBalance := left.hom.balance
  rw [leftLinear, leftDivisorEq] at leftBalance
  have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
  rw [degreeOne, one_nsmul]
  rw [degreeOne, one_nsmul] at leftBalance
  have leftClassEq :
      gpPullback Phi left.hom.base left.target.divisorClass =
        object.divisorClass +
            (Algebra.GrothendieckAddGroup.of leftDivisor :
              Algebra.GrothendieckAddGroup
                (Phi.obj (Object.base object)).carrier) -
          data.divisor (Object.base object) left.hom.rationalFunction := by
    apply eq_sub_of_add_eq
    exact leftBalance.symm
  have rightLinear := right.preStep.1
  change right.hom.frobeniusDegree = 1 at rightLinear
  have rightDivisorEq := right.divisor_eq
  change right.hom.divisor = rightDivisor at rightDivisorEq
  have rightBalance := right.hom.balance
  rw [rightLinear, rightDivisorEq] at rightBalance
  rw [degreeOne, one_nsmul] at rightBalance
  have rightClassEq :
      gpPullback Phi right.hom.base right.target.divisorClass =
        object.divisorClass +
            (Algebra.GrothendieckAddGroup.of rightDivisor :
              Algebra.GrothendieckAddGroup
                (Phi.obj (Object.base object)).carrier) -
          data.divisor (Object.base object) right.hom.rationalFunction := by
    apply eq_sub_of_add_eq
    exact rightBalance.symm
  have divisorClassEquality :
      (Algebra.GrothendieckAddGroup.of rightDivisor :
          Algebra.GrothendieckAddGroup
            (Phi.obj (Object.base object)).carrier) =
        Algebra.GrothendieckAddGroup.of leftDivisor +
          Algebra.GrothendieckAddGroup.of remainder := by
    rw [divisorEquality]
    exact (Algebra.GrothendieckAddGroup.of
      (M := (preFrobenioid Phi data).DivisorOrder object)).map_add
        leftDivisor remainder
  rw [leftClassEq, rightClassEq, divisorClassEquality, map_sub]
  abel_nf
  ac_rfl

theorem epi_of_baseIsIso
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (baseIsIso : IsIso arrow.base) : Epi arrow := by
  letI : IsIso arrow.base := baseIsIso
  constructor
  intro next first second equality
  have degreeEquality :
      first.frobeniusDegree = second.frobeniusDegree := by
    have projected := congrArg Hom.frobeniusDegree equality
    change arrow.frobeniusDegree * first.frobeniusDegree =
      arrow.frobeniusDegree * second.frobeniusDegree at projected
    exact mul_left_cancel projected
  have baseEquality : first.base = second.base := by
    have projected := congrArg Hom.base equality
    change arrow.base ≫ first.base = arrow.base ≫ second.base at projected
    exact (cancel_epi arrow.base).mp projected
  have divisorEquality : first.divisor = second.divisor := by
    have projected := congrArg Hom.divisor equality
    change Phi.pullback arrow.base first.divisor +
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
      simpa only [add_comm] using projected
    exact (Phi.obj (Object.base source)).integral
      (second.frobeniusDegree.val • arrow.divisor)
      (Phi.pullback arrow.base first.divisor)
      (Phi.pullback arrow.base second.divisor) cancellable
  have rationalFunctionEquality :
      first.rationalFunction = second.rationalFunction := by
    have projected := congrArg Hom.rationalFunction equality
    change data.rationalFunctions.pullback arrow.base
            first.rationalFunction +
          first.frobeniusDegree.val • arrow.rationalFunction =
        data.rationalFunctions.pullback arrow.base
            second.rationalFunction +
          second.frobeniusDegree.val • arrow.rationalFunction at projected
    rw [degreeEquality] at projected
    apply data.rationalFunctions.pullback_injective arrow.base
    exact add_right_cancel projected
  exact Hom.ext degreeEquality baseEquality divisorEquality
    rationalFunctionEquality

theorem outgoingDivisorComparison_comp
    {object : Carrier Phi data}
    {leftDivisor rightDivisor :
      (preFrobenioid Phi data).DivisorOrder object}
    (left : (preFrobenioid Phi data).OutgoingCoAngularPreStep
      object leftDivisor)
    (right : (preFrobenioid Phi data).OutgoingCoAngularPreStep
      object rightDivisor)
    (remainder : (preFrobenioid Phi data).DivisorOrder object)
    (divisorEquality : rightDivisor = leftDivisor + remainder) :
    left.hom ≫ outgoingDivisorComparison left right remainder
      divisorEquality = right.hom := by
  have leftBaseIsIso := left.preStep.2
  change IsIso left.hom.base at leftBaseIsIso
  letI : IsIso left.hom.base := leftBaseIsIso
  apply Hom.ext
  · rw [comp_frobeniusDegree]
    change left.hom.frobeniusDegree * 1 = right.hom.frobeniusDegree
    have leftLinear := left.preStep.1
    change left.hom.frobeniusDegree = 1 at leftLinear
    have rightLinear := right.preStep.1
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftLinear, rightLinear]
    rfl
  · rw [comp_base]
    change left.hom.base ≫
      (inv left.hom.base ≫ right.hom.base) = right.hom.base
    simp
  · rw [comp_divisor]
    change Phi.pullback left.hom.base
          (Phi.pullback (inv left.hom.base) remainder) +
        (1 : ℕ+).val • left.hom.divisor = right.hom.divisor
    rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
      IsIso.hom_inv_id, Phi.pullback_id]
    have leftDivisorEq := left.divisor_eq
    change left.hom.divisor = leftDivisor at leftDivisorEq
    have rightDivisorEq := right.divisor_eq
    change right.hom.divisor = rightDivisor at rightDivisorEq
    have divisorEqualityCarrier :
        (show (Phi.obj (Object.base object)).carrier from rightDivisor) =
          (show (Phi.obj (Object.base object)).carrier from leftDivisor) +
            (show (Phi.obj (Object.base object)).carrier from remainder) :=
      divisorEquality
    have divisorEquality' :
        right.hom.divisor = left.hom.divisor +
          (show (Phi.obj (Object.base object)).carrier from remainder) := by
      calc
        right.hom.divisor =
            (show (Phi.obj (Object.base object)).carrier from rightDivisor) :=
          rightDivisorEq
        _ = (show (Phi.obj (Object.base object)).carrier from leftDivisor) +
              (show (Phi.obj (Object.base object)).carrier from remainder) :=
          divisorEqualityCarrier
        _ = left.hom.divisor +
              (show (Phi.obj (Object.base object)).carrier from remainder) := by
          rw [leftDivisorEq]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    simpa only [AddMonoidHom.id_apply, add_comm] using divisorEquality'.symm
  · rw [comp_rationalFunction]
    change data.rationalFunctions.pullback left.hom.base
          (data.rationalFunctions.pullback (inv left.hom.base)
            (right.hom.rationalFunction - left.hom.rationalFunction)) +
        (1 : ℕ+).val • left.hom.rationalFunction =
      right.hom.rationalFunction
    rw [← AddMonoidHom.comp_apply,
      ← data.rationalFunctions.pullback_comp,
      IsIso.hom_inv_id, data.rationalFunctions.pullback_id]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    simp only [AddMonoidHom.id_apply]
    abel

theorem outgoingDivisorOrderFullyFaithful
    {object : Carrier Phi data}
    {leftDivisor rightDivisor :
      (preFrobenioid Phi data).DivisorOrder object}
    (left : (preFrobenioid Phi data).OutgoingCoAngularPreStep
      object leftDivisor)
    (right : (preFrobenioid Phi data).OutgoingCoAngularPreStep
      object rightDivisor) :
    leftDivisor ≤ rightDivisor ↔
      ∃! f : left.target ⟶ right.target, left.hom ≫ f = right.hom := by
  constructor
  · rintro ⟨remainder, divisorEquality⟩
    let comparison := outgoingDivisorComparison left right remainder
      divisorEquality
    refine ⟨comparison,
      outgoingDivisorComparison_comp left right remainder divisorEquality,
      ?_⟩
    intro other otherComp
    have leftBaseIsIso := left.preStep.2
    change IsIso left.hom.base at leftBaseIsIso
    letI : Epi left.hom := epi_of_baseIsIso left.hom leftBaseIsIso
    exact (cancel_epi left.hom).mp
      (otherComp.trans
        (outgoingDivisorComparison_comp left right remainder
          divisorEquality).symm)
  · rintro ⟨comparison, comparisonComp, _⟩
    refine ⟨Phi.pullback left.hom.base comparison.divisor, ?_⟩
    have projected := congrArg Hom.divisor comparisonComp
    change Phi.pullback left.hom.base comparison.divisor +
          comparison.frobeniusDegree.val • left.hom.divisor =
        right.hom.divisor at projected
    have degreeProjected := congrArg Hom.frobeniusDegree comparisonComp
    change left.hom.frobeniusDegree * comparison.frobeniusDegree =
      right.hom.frobeniusDegree at degreeProjected
    have leftLinear := left.preStep.1
    change left.hom.frobeniusDegree = 1 at leftLinear
    have rightLinear := right.preStep.1
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftLinear, rightLinear] at degreeProjected
    have comparisonLinear : comparison.frobeniusDegree = 1 := by
      simpa using degreeProjected
    rw [comparisonLinear] at projected
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul] at projected
    have leftDivisorEq := left.divisor_eq
    change left.hom.divisor = leftDivisor at leftDivisorEq
    have rightDivisorEq := right.divisor_eq
    change right.hom.divisor = rightDivisor at rightDivisorEq
    rw [leftDivisorEq, rightDivisorEq] at projected
    simpa only [add_comm] using projected.symm

theorem outgoingDivisorRepresentative_unique
    {object : Carrier Phi data}
    {divisor : (preFrobenioid Phi data).DivisorOrder object}
    (left right : (preFrobenioid Phi data).OutgoingCoAngularPreStep
      object divisor) :
    ∃! e : left.target ≅ right.target,
      left.hom ≫ e.hom = right.hom := by
  rcases (outgoingDivisorOrderFullyFaithful left right).1 (le_refl divisor) with
    ⟨forward, forwardComp, forwardUnique⟩
  rcases (outgoingDivisorOrderFullyFaithful right left).1 (le_refl divisor) with
    ⟨backward, backwardComp, backwardUnique⟩
  have leftBaseIsIso := left.preStep.2
  change IsIso left.hom.base at leftBaseIsIso
  letI : Epi left.hom := epi_of_baseIsIso left.hom leftBaseIsIso
  have rightBaseIsIso := right.preStep.2
  change IsIso right.hom.base at rightBaseIsIso
  letI : Epi right.hom := epi_of_baseIsIso right.hom rightBaseIsIso
  have forwardBackward : forward ≫ backward = 𝟙 left.target := by
    apply (cancel_epi left.hom).mp
    rw [← Category.assoc, forwardComp, backwardComp, Category.comp_id]
  have backwardForward : backward ≫ forward = 𝟙 right.target := by
    apply (cancel_epi right.hom).mp
    rw [← Category.assoc, backwardComp, forwardComp, Category.comp_id]
  let comparison : left.target ≅ right.target :=
    { hom := forward
      inv := backward
      hom_inv_id := forwardBackward
      inv_hom_id := backwardForward }
  refine ⟨comparison, forwardComp, ?_⟩
  intro other otherComp
  apply Iso.ext
  exact forwardUnique other.hom otherComp

/-- The source obtained by subtracting an effective divisor. -/
def incomingDivisorSource (object : Carrier Phi data)
    (divisor : (Phi.obj (Object.base object)).carrier) :
    Carrier Phi data where
  base := Object.base object
  divisorClass := object.divisorClass -
    Algebra.GrothendieckAddGroup.of divisor

def incomingDivisorArrow (object : Carrier Phi data)
    (divisor : (Phi.obj (Object.base object)).carrier) :
    incomingDivisorSource object divisor ⟶ object where
  frobeniusDegree := 1
  base := 𝟙 (Object.base object)
  divisor := divisor
  rationalFunction := 0
  balance := by
    dsimp only [incomingDivisorSource]
    rw [gpPullback_id]
    change (1 : ℕ) •
          (object.divisorClass - Algebra.GrothendieckAddGroup.of divisor) +
        Algebra.GrothendieckAddGroup.of divisor =
      object.divisorClass + data.divisor (Object.base object) 0
    simp only [one_nsmul, map_zero, add_zero]
    abel

def incomingDivisorRepresentative (object : Carrier Phi data)
    (divisor : (preFrobenioid Phi data).DivisorOrder object) :
    (preFrobenioid Phi data).IncomingCoAngularPreStep object divisor where
  source := incomingDivisorSource object divisor
  hom := incomingDivisorArrow object divisor
  preStep := by
    constructor
    · rfl
    · change IsIso (𝟙 (Object.base object))
      infer_instance
  coAngular := isCoAngular Phi data (incomingDivisorArrow object divisor)
  pulledBack_divisor_eq := by
    change Phi.pullback (𝟙 (Object.base object)) divisor = divisor
    rw [Phi.pullback_id]
    rfl

theorem incomingDivisor
    {object source : Carrier Phi data} (arrow : source ⟶ object)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) :
    ∃! divisor : (preFrobenioid Phi data).DivisorOrder object,
      Phi.pullback arrow.base divisor = arrow.divisor := by
  have baseIsIso := preStep.2
  change IsIso arrow.base at baseIsIso
  letI : IsIso arrow.base := baseIsIso
  let divisor := Phi.pullback (inv arrow.base) arrow.divisor
  have realizes : Phi.pullback arrow.base divisor = arrow.divisor := by
    dsimp only [divisor]
    rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
      IsIso.hom_inv_id, Phi.pullback_id]
    rfl
  refine ⟨divisor, realizes, ?_⟩
  intro other otherRealizes
  apply Phi.characteristicallyInjective arrow.base
  exact otherRealizes.trans realizes.symm

def incomingDivisorComparison
    {object : Carrier Phi data}
    {leftDivisor rightDivisor :
      (preFrobenioid Phi data).DivisorOrder object}
    (left : (preFrobenioid Phi data).IncomingCoAngularPreStep
      object leftDivisor)
    (right : (preFrobenioid Phi data).IncomingCoAngularPreStep
      object rightDivisor)
    (remainder : (preFrobenioid Phi data).DivisorOrder object)
    (divisorEquality : leftDivisor = rightDivisor + remainder) :
    left.source ⟶ right.source := by
  have leftBaseIsIso := left.preStep.2
  change IsIso left.hom.base at leftBaseIsIso
  letI : IsIso left.hom.base := leftBaseIsIso
  have rightBaseIsIso := right.preStep.2
  change IsIso right.hom.base at rightBaseIsIso
  letI : IsIso right.hom.base := rightBaseIsIso
  let baseComparison := left.hom.base ≫ inv right.hom.base
  have baseComparison_comp :
      baseComparison ≫ right.hom.base = left.hom.base := by
    dsimp only [baseComparison]
    simp
  have rightDivisorTransport :
      Phi.pullback baseComparison right.hom.divisor =
        Phi.pullback left.hom.base rightDivisor := by
    have rightAssigned := right.pulledBack_divisor_eq
    change Phi.pullback right.hom.base rightDivisor =
      right.hom.divisor at rightAssigned
    rw [← rightAssigned]
    rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
      baseComparison_comp]
  have divisorEqualityCarrier :
      (show (Phi.obj (Object.base object)).carrier from leftDivisor) =
        (show (Phi.obj (Object.base object)).carrier from rightDivisor) +
          (show (Phi.obj (Object.base object)).carrier from remainder) :=
    divisorEquality
  have divisorDecomp :
      left.hom.divisor =
        Phi.pullback baseComparison right.hom.divisor +
          Phi.pullback left.hom.base remainder := by
    have leftAssigned := left.pulledBack_divisor_eq
    change Phi.pullback left.hom.base leftDivisor =
      left.hom.divisor at leftAssigned
    have mappedDivisorEquality :
        Phi.pullback left.hom.base leftDivisor =
          Phi.pullback left.hom.base rightDivisor +
            Phi.pullback left.hom.base remainder := by
      calc
        Phi.pullback left.hom.base leftDivisor =
            Phi.pullback left.hom.base
              ((show (Phi.obj (Object.base object)).carrier from rightDivisor) +
                (show (Phi.obj (Object.base object)).carrier from remainder)) :=
          congrArg (Phi.pullback left.hom.base) divisorEqualityCarrier
        _ = _ := map_add _ _ _
    calc
      left.hom.divisor =
          Phi.pullback left.hom.base leftDivisor := leftAssigned.symm
      _ = Phi.pullback left.hom.base rightDivisor +
          Phi.pullback left.hom.base remainder := mappedDivisorEquality
      _ = Phi.pullback baseComparison right.hom.divisor +
          Phi.pullback left.hom.base remainder := by
        rw [rightDivisorTransport]
  refine
    { frobeniusDegree := 1
      base := baseComparison
      divisor := Phi.pullback left.hom.base remainder
      rationalFunction := left.hom.rationalFunction -
        data.rationalFunctions.pullback baseComparison
          right.hom.rationalFunction
      balance := ?_ }
  have leftLinear := left.preStep.1
  change left.hom.frobeniusDegree = 1 at leftLinear
  have leftBalance := left.hom.balance
  rw [leftLinear] at leftBalance
  have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
  rw [degreeOne, one_nsmul] at leftBalance
  have leftClassEq :
      left.source.divisorClass =
        gpPullback Phi left.hom.base object.divisorClass +
            data.divisor (Object.base left.source)
              left.hom.rationalFunction -
          Algebra.GrothendieckAddGroup.of left.hom.divisor := by
    apply eq_sub_of_add_eq
    exact leftBalance
  have rightLinear := right.preStep.1
  change right.hom.frobeniusDegree = 1 at rightLinear
  have rightBalance := right.hom.balance
  rw [rightLinear] at rightBalance
  rw [degreeOne, one_nsmul] at rightBalance
  have rightClassEq :
      right.source.divisorClass =
        gpPullback Phi right.hom.base object.divisorClass +
            data.divisor (Object.base right.source)
              right.hom.rationalFunction -
          Algebra.GrothendieckAddGroup.of right.hom.divisor := by
    apply eq_sub_of_add_eq
    exact rightBalance
  have classTransport :
      gpPullback Phi baseComparison right.source.divisorClass =
        gpPullback Phi left.hom.base object.divisorClass +
            data.divisor (Object.base left.source)
              (data.rationalFunctions.pullback baseComparison
                right.hom.rationalFunction) -
          Algebra.GrothendieckAddGroup.of
            (Phi.pullback baseComparison right.hom.divisor) := by
    rw [rightClassEq]
    simp only [map_add, map_sub, gpPullback_of]
    rw [← data.divisor_natural]
    rw [← AddMonoidHom.comp_apply, ← gpPullback_comp,
      baseComparison_comp]
  have divisorClassDecomp :
      Algebra.GrothendieckAddGroup.of left.hom.divisor =
        Algebra.GrothendieckAddGroup.of
            (Phi.pullback baseComparison right.hom.divisor) +
          Algebra.GrothendieckAddGroup.of
            (Phi.pullback left.hom.base remainder) := by
    rw [divisorDecomp, map_add]
  change (1 : ℕ) • left.source.divisorClass +
        Algebra.GrothendieckAddGroup.of
          (Phi.pullback left.hom.base remainder) =
      gpPullback Phi baseComparison right.source.divisorClass +
        data.divisor (Object.base left.source)
          (left.hom.rationalFunction -
            data.rationalFunctions.pullback baseComparison
              right.hom.rationalFunction)
  rw [one_nsmul, leftClassEq, classTransport, map_sub,
    divisorClassDecomp]
  abel

theorem incomingDivisorComparison_comp
    {object : Carrier Phi data}
    {leftDivisor rightDivisor :
      (preFrobenioid Phi data).DivisorOrder object}
    (left : (preFrobenioid Phi data).IncomingCoAngularPreStep
      object leftDivisor)
    (right : (preFrobenioid Phi data).IncomingCoAngularPreStep
      object rightDivisor)
    (remainder : (preFrobenioid Phi data).DivisorOrder object)
    (divisorEquality : leftDivisor = rightDivisor + remainder) :
    incomingDivisorComparison left right remainder divisorEquality ≫
      right.hom = left.hom := by
  have leftBaseIsIso := left.preStep.2
  change IsIso left.hom.base at leftBaseIsIso
  letI : IsIso left.hom.base := leftBaseIsIso
  have rightBaseIsIso := right.preStep.2
  change IsIso right.hom.base at rightBaseIsIso
  letI : IsIso right.hom.base := rightBaseIsIso
  apply Hom.ext
  · rw [comp_frobeniusDegree]
    change 1 * right.hom.frobeniusDegree = left.hom.frobeniusDegree
    have leftLinear := left.preStep.1
    change left.hom.frobeniusDegree = 1 at leftLinear
    have rightLinear := right.preStep.1
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftLinear, rightLinear]
    exact one_mul 1
  · rw [comp_base]
    change (left.hom.base ≫ inv right.hom.base) ≫ right.hom.base =
      left.hom.base
    simp
  · rw [comp_divisor]
    change Phi.pullback (left.hom.base ≫ inv right.hom.base)
          right.hom.divisor +
        right.hom.frobeniusDegree.val •
          Phi.pullback left.hom.base remainder = left.hom.divisor
    have rightLinear := right.preStep.1
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [rightLinear]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    have rightAssigned := right.pulledBack_divisor_eq
    change Phi.pullback right.hom.base rightDivisor =
      right.hom.divisor at rightAssigned
    have rightTransport :
        Phi.pullback (left.hom.base ≫ inv right.hom.base)
            right.hom.divisor =
          Phi.pullback left.hom.base rightDivisor := by
      rw [← rightAssigned, ← AddMonoidHom.comp_apply,
        ← Phi.pullback_comp]
      simp
    rw [rightTransport]
    have leftAssigned := left.pulledBack_divisor_eq
    change Phi.pullback left.hom.base leftDivisor =
      left.hom.divisor at leftAssigned
    rw [← leftAssigned]
    have divisorEqualityCarrier :
        (show (Phi.obj (Object.base object)).carrier from leftDivisor) =
          (show (Phi.obj (Object.base object)).carrier from rightDivisor) +
            (show (Phi.obj (Object.base object)).carrier from remainder) :=
      divisorEquality
    calc
      Phi.pullback left.hom.base rightDivisor +
          Phi.pullback left.hom.base remainder =
          Phi.pullback left.hom.base
            ((show (Phi.obj (Object.base object)).carrier from rightDivisor) +
              (show (Phi.obj (Object.base object)).carrier from remainder)) :=
        (map_add _ _ _).symm
      _ = Phi.pullback left.hom.base leftDivisor :=
        congrArg (Phi.pullback left.hom.base) divisorEqualityCarrier.symm
  · rw [comp_rationalFunction]
    change data.rationalFunctions.pullback
          (left.hom.base ≫ inv right.hom.base) right.hom.rationalFunction +
        right.hom.frobeniusDegree.val •
          (left.hom.rationalFunction -
            data.rationalFunctions.pullback
              (left.hom.base ≫ inv right.hom.base)
                right.hom.rationalFunction) =
      left.hom.rationalFunction
    have rightLinear := right.preStep.1
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [rightLinear]
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul]
    abel

theorem mono_of_preStep
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (preStep : (preFrobenioid Phi data).IsPreStep arrow) : Mono arrow := by
  have baseIsIso := preStep.2
  change IsIso arrow.base at baseIsIso
  letI : IsIso arrow.base := baseIsIso
  have linear := preStep.1
  change arrow.frobeniusDegree = 1 at linear
  constructor
  intro prior first second equality
  have degreeEquality :
      first.frobeniusDegree = second.frobeniusDegree := by
    have projected := congrArg Hom.frobeniusDegree equality
    change first.frobeniusDegree * arrow.frobeniusDegree =
      second.frobeniusDegree * arrow.frobeniusDegree at projected
    rw [linear] at projected
    simpa using projected
  have baseEquality : first.base = second.base := by
    have projected := congrArg Hom.base equality
    change first.base ≫ arrow.base = second.base ≫ arrow.base at projected
    exact (cancel_mono arrow.base).mp projected
  have divisorEquality : first.divisor = second.divisor := by
    have projected := congrArg Hom.divisor equality
    change Phi.pullback first.base arrow.divisor +
          arrow.frobeniusDegree.val • first.divisor =
        Phi.pullback second.base arrow.divisor +
          arrow.frobeniusDegree.val • second.divisor at projected
    rw [baseEquality, linear] at projected
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul, one_nsmul] at projected
    exact (Phi.obj (Object.base prior)).integral
      (Phi.pullback second.base arrow.divisor)
      first.divisor second.divisor projected
  have rationalFunctionEquality :
      first.rationalFunction = second.rationalFunction := by
    have projected := congrArg Hom.rationalFunction equality
    change data.rationalFunctions.pullback first.base arrow.rationalFunction +
          arrow.frobeniusDegree.val • first.rationalFunction =
        data.rationalFunctions.pullback second.base arrow.rationalFunction +
          arrow.frobeniusDegree.val • second.rationalFunction at projected
    rw [baseEquality, linear] at projected
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul, one_nsmul] at projected
    exact add_left_cancel projected
  exact Hom.ext degreeEquality baseEquality divisorEquality
    rationalFunctionEquality

theorem incomingDivisorOrderFullyFaithful
    {object : Carrier Phi data}
    {leftDivisor rightDivisor :
      (preFrobenioid Phi data).DivisorOrder object}
    (left : (preFrobenioid Phi data).IncomingCoAngularPreStep
      object leftDivisor)
    (right : (preFrobenioid Phi data).IncomingCoAngularPreStep
      object rightDivisor) :
    rightDivisor ≤ leftDivisor ↔
      ∃! f : left.source ⟶ right.source, f ≫ right.hom = left.hom := by
  constructor
  · rintro ⟨remainder, divisorEquality⟩
    let comparison := incomingDivisorComparison left right remainder
      divisorEquality
    refine ⟨comparison,
      incomingDivisorComparison_comp left right remainder divisorEquality,
      ?_⟩
    intro other otherComp
    have rightMono : Mono right.hom := mono_of_preStep right.hom right.preStep
    letI : Mono right.hom := rightMono
    exact (cancel_mono right.hom).mp
      (otherComp.trans
        (incomingDivisorComparison_comp left right remainder
          divisorEquality).symm)
  · rintro ⟨comparison, comparisonComp, _⟩
    have leftBaseIsIso := left.preStep.2
    change IsIso left.hom.base at leftBaseIsIso
    letI : IsIso left.hom.base := leftBaseIsIso
    have rightBaseIsIso := right.preStep.2
    change IsIso right.hom.base at rightBaseIsIso
    letI : IsIso right.hom.base := rightBaseIsIso
    refine ⟨Phi.pullback (inv left.hom.base) comparison.divisor, ?_⟩
    have baseProjected := congrArg Hom.base comparisonComp
    change comparison.base ≫ right.hom.base = left.hom.base at baseProjected
    have degreeProjected := congrArg Hom.frobeniusDegree comparisonComp
    change comparison.frobeniusDegree * right.hom.frobeniusDegree =
      left.hom.frobeniusDegree at degreeProjected
    have leftLinear := left.preStep.1
    change left.hom.frobeniusDegree = 1 at leftLinear
    have rightLinear := right.preStep.1
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftLinear, rightLinear] at degreeProjected
    have comparisonLinear : comparison.frobeniusDegree = 1 := by
      simpa using degreeProjected
    have divisorProjected := congrArg Hom.divisor comparisonComp
    change Phi.pullback comparison.base right.hom.divisor +
          right.hom.frobeniusDegree.val • comparison.divisor =
        left.hom.divisor at divisorProjected
    rw [rightLinear] at divisorProjected
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul] at divisorProjected
    have leftAssigned := left.pulledBack_divisor_eq
    change Phi.pullback left.hom.base leftDivisor =
      left.hom.divisor at leftAssigned
    have rightAssigned := right.pulledBack_divisor_eq
    change Phi.pullback right.hom.base rightDivisor =
      right.hom.divisor at rightAssigned
    rw [← leftAssigned, ← rightAssigned] at divisorProjected
    have transported := congrArg (Phi.pullback (inv left.hom.base))
      divisorProjected
    simp only [map_add] at transported
    have rightCancel :
        Phi.pullback (inv left.hom.base)
            (Phi.pullback comparison.base
              (Phi.pullback right.hom.base rightDivisor)) = rightDivisor := by
      rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp]
      rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
        Category.assoc, baseProjected, IsIso.inv_hom_id, Phi.pullback_id]
      rfl
    have leftCancel :
        Phi.pullback (inv left.hom.base)
            (Phi.pullback left.hom.base leftDivisor) = leftDivisor := by
      rw [← AddMonoidHom.comp_apply, ← Phi.pullback_comp,
        IsIso.inv_hom_id, Phi.pullback_id]
      rfl
    rw [rightCancel, leftCancel] at transported
    simpa only [AddMonoidHom.id_apply] using transported.symm

theorem incomingDivisorRepresentative_unique
    {object : Carrier Phi data}
    {divisor : (preFrobenioid Phi data).DivisorOrder object}
    (left right : (preFrobenioid Phi data).IncomingCoAngularPreStep
      object divisor) :
    ∃! e : left.source ≅ right.source,
      e.hom ≫ right.hom = left.hom := by
  rcases (incomingDivisorOrderFullyFaithful left right).1 (le_refl divisor) with
    ⟨forward, forwardComp, forwardUnique⟩
  rcases (incomingDivisorOrderFullyFaithful right left).1 (le_refl divisor) with
    ⟨backward, backwardComp, backwardUnique⟩
  have leftMono : Mono left.hom := mono_of_preStep left.hom left.preStep
  letI : Mono left.hom := leftMono
  have rightMono : Mono right.hom := mono_of_preStep right.hom right.preStep
  letI : Mono right.hom := rightMono
  have forwardBackward : forward ≫ backward = 𝟙 left.source := by
    apply (cancel_mono left.hom).mp
    rw [Category.assoc, backwardComp, forwardComp, Category.id_comp]
  have backwardForward : backward ≫ forward = 𝟙 right.source := by
    apply (cancel_mono right.hom).mp
    rw [Category.assoc, forwardComp, backwardComp, Category.id_comp]
  let comparison : left.source ≅ right.source :=
    { hom := forward
      inv := backward
      hom_inv_id := forwardBackward
      inv_hom_id := backwardForward }
  refine ⟨comparison, forwardComp, ?_⟩
  intro other otherComp
  apply Iso.ext
  exact forwardUnique other.hom otherComp

end
end Iut.SourceModelFrobenioid.Carrier
