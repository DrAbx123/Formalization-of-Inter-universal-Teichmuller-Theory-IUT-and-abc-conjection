/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidDivisorOrder

/-!
# Arbitrary-arrow factorizations for the source model Frobenioid

This file implements the existence half of Frobenioids I, Definition
1.3(iv)(a), by separating an arbitrary model arrow into its Frobenius degree,
effective divisor and rational function, and base pullback.  It also proves
Definition 1.3(iv)(b) from the representable universal property of pullback
morphisms.  Essential uniqueness of the three-stage factorization is handled
separately.
-/

open CategoryTheory
namespace Iut.SourceModelFrobenioid.Carrier
universe u
noncomputable section
variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- The middle arrow in the canonical Definition 1.3(iv)(a) factorization. -/
def factorizationPreStep
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    frobeniusCodomain Phi data source arrow.frobeniusDegree ⟶
      pullbackObject Phi data target arrow.base where
  frobeniusDegree := 1
  base := 𝟙 (Object.base source)
  divisor := arrow.divisor
  rationalFunction := arrow.rationalFunction
  balance := by
    dsimp only [frobeniusCodomain, pullbackObject]
    rw [gpPullback_id]
    change (1 : ℕ) • arrow.frobeniusDegree.val • source.divisorClass +
        Algebra.GrothendieckAddGroup.of arrow.divisor =
      gpPullback Phi arrow.base target.divisorClass +
        data.divisor (Object.base source) arrow.rationalFunction
    rw [one_nsmul]
    exact arrow.balance

theorem factorizationPreStep_isPreStep
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid Phi data).IsPreStep (factorizationPreStep arrow) := by
  constructor
  · rfl
  · change IsIso (𝟙 (Object.base source))
    infer_instance

theorem factorization_composite
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    frobeniusArrow Phi data source arrow.frobeniusDegree ≫
        factorizationPreStep arrow ≫
          pullbackArrow Phi data target arrow.base =
      arrow := by
  apply Hom.ext
  · rw [comp_frobeniusDegree, comp_frobeniusDegree]
    dsimp only [frobeniusArrow, factorizationPreStep, pullbackArrow]
    simp
  · rw [comp_base, comp_base]
    dsimp only [frobeniusArrow, factorizationPreStep, pullbackArrow]
    exact (Category.id_comp (𝟙 (Object.base source) ≫ arrow.base)).trans
      (Category.id_comp arrow.base)
  · rw [comp_divisor, comp_divisor]
    dsimp only [frobeniusArrow, factorizationPreStep, pullbackArrow]
    simp only [map_zero, zero_add, nsmul_zero, add_zero]
    change Phi.pullback (𝟙 (Object.base source))
      ((1 : ℕ) • arrow.divisor) = arrow.divisor
    rw [one_nsmul]
    exact DFunLike.congr_fun (Phi.pullback_id (Object.base source))
      arrow.divisor
  · rw [comp_rationalFunction, comp_rationalFunction]
    dsimp only [frobeniusArrow, factorizationPreStep, pullbackArrow]
    simp only [map_zero, zero_add, nsmul_zero, add_zero]
    change data.rationalFunctions.pullback (𝟙 (Object.base source))
      ((1 : ℕ) • arrow.rationalFunction) = arrow.rationalFunction
    rw [one_nsmul]
    exact DFunLike.congr_fun
      (data.rationalFunctions.pullback_id (Object.base source))
        arrow.rationalFunction

/-- Definition 1.3(iv)(a)'s explicit factorization in the model category. -/
def factorization
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid Phi data).FrobenioidFactorization arrow where
  frobeniusCodomain :=
    frobeniusCodomain Phi data source arrow.frobeniusDegree
  preStepCodomain := pullbackObject Phi data target arrow.base
  frobenius := frobeniusArrow Phi data source arrow.frobeniusDegree
  preStep := factorizationPreStep arrow
  pullback := pullbackArrow Phi data target arrow.base
  frobenius_type :=
    frobeniusArrow_ofFrobeniusType Phi data source arrow.frobeniusDegree
  preStep_type := factorizationPreStep_isPreStep arrow
  pullback_type := pullbackArrow_isPullback Phi data target arrow.base
  composite := factorization_composite arrow

/-- Every isomorphism in the model category is linear and isometric. -/
theorem isIso_linear_isometric
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    [IsIso arrow] :
    (preFrobenioid Phi data).IsLinear arrow ∧
      (preFrobenioid Phi data).IsIsometric arrow := by
  have inverseDegreeOne : (inv arrow).frobeniusDegree = 1 := by
    have projected := congrArg Hom.frobeniusDegree
      (IsIso.hom_inv_id arrow)
    change arrow.frobeniusDegree * (inv arrow).frobeniusDegree = 1 at projected
    apply Subtype.ext
    have projectedVal := congrArg (fun degree : ℕ+ ↦ degree.val) projected
    exact Nat.eq_one_of_mul_eq_one_left projectedVal
  have arrowDegreeOne : arrow.frobeniusDegree = 1 := by
    have projected := congrArg Hom.frobeniusDegree
      (IsIso.hom_inv_id arrow)
    change arrow.frobeniusDegree * (inv arrow).frobeniusDegree = 1 at projected
    apply Subtype.ext
    have projectedVal := congrArg (fun degree : ℕ+ ↦ degree.val) projected
    exact Nat.eq_one_of_mul_eq_one_right projectedVal
  constructor
  · exact arrowDegreeOne
  · have projected := congrArg Hom.divisor (IsIso.hom_inv_id arrow)
    change Phi.pullback arrow.base (inv arrow).divisor +
        (inv arrow).frobeniusDegree.val • arrow.divisor = 0 at projected
    rw [inverseDegreeOne] at projected
    have degreeOne : (1 : ℕ+).val = (1 : ℕ) := rfl
    rw [degreeOne, one_nsmul] at projected
    apply (Phi.obj (Object.base source)).sharp arrow.divisor
    rw [isAddUnit_iff_exists]
    refine ⟨Phi.pullback arrow.base (inv arrow).divisor, ?_, projected⟩
    simpa only [add_comm] using projected

/-- Definition 1.3(iv)(b) for an arbitrary model pullback morphism. -/
theorem pullback_linear_lbInvertible
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (arrowPullback : (preFrobenioid Phi data).IsPullback arrow) :
    (preFrobenioid Phi data).IsLinear arrow ∧
      (preFrobenioid Phi data).IsLBInvertible arrow := by
  let canonicalSource := pullbackObject Phi data target arrow.base
  let canonical := pullbackArrow Phi data target arrow.base
  have canonicalPullback :
      (preFrobenioid Phi data).IsPullback canonical :=
    pullbackArrow_isPullback Phi data target arrow.base
  let toCanonical :
      (preFrobenioid Phi data).PullbackComparisonTarget canonical source :=
    { toCodomain := arrow
      toBaseDomain := 𝟙 (Object.base source)
      commutes := by
        change arrow.base = 𝟙 (Object.base source) ≫ arrow.base
        simp }
  rcases (canonicalPullback source).2 toCanonical with
    ⟨forward, forwardComparison⟩
  have forwardComp : forward ≫ canonical = arrow := by
    exact congrArg
      PreFrobenioid.PullbackComparisonTarget.toCodomain forwardComparison
  have forwardBase : forward.base = 𝟙 (Object.base source) := by
    exact congrArg
      PreFrobenioid.PullbackComparisonTarget.toBaseDomain forwardComparison
  let toArrow :
      (preFrobenioid Phi data).PullbackComparisonTarget arrow canonicalSource :=
    { toCodomain := canonical
      toBaseDomain := 𝟙 (Object.base source)
      commutes := by
        change arrow.base = 𝟙 (Object.base source) ≫ arrow.base
        simp }
  rcases (arrowPullback canonicalSource).2 toArrow with
    ⟨backward, backwardComparison⟩
  have backwardComp : backward ≫ arrow = canonical := by
    exact congrArg
      PreFrobenioid.PullbackComparisonTarget.toCodomain backwardComparison
  have backwardBase : backward.base = 𝟙 (Object.base source) := by
    exact congrArg
      PreFrobenioid.PullbackComparisonTarget.toBaseDomain backwardComparison
  have forwardBackward : forward ≫ backward = 𝟙 source := by
    apply (arrowPullback source).1
    apply pullbackComparisonTarget_ext Phi data
    · change (forward ≫ backward) ≫ arrow = 𝟙 source ≫ arrow
      rw [Category.assoc, backwardComp, forwardComp]
      simp
    · change (forward ≫ backward).base = 𝟙 (Object.base source)
      rw [comp_base, forwardBase, backwardBase]
      exact Category.id_comp _
  have backwardForward : backward ≫ forward = 𝟙 canonicalSource := by
    apply (canonicalPullback canonicalSource).1
    apply pullbackComparisonTarget_ext Phi data
    · change (backward ≫ forward) ≫ canonical =
        𝟙 canonicalSource ≫ canonical
      rw [Category.assoc, forwardComp, backwardComp]
      simp
    · change (backward ≫ forward).base =
        𝟙 (Object.base canonicalSource)
      rw [comp_base, backwardBase, forwardBase]
      change 𝟙 (Object.base source) ≫ 𝟙 (Object.base source) =
        𝟙 (Object.base source)
      exact Category.id_comp _
  letI : IsIso forward := IsIso.mk
    ⟨backward, forwardBackward, backwardForward⟩
  have forwardType := isIso_linear_isometric forward
  have forwardLinear := forwardType.1
  change forward.frobeniusDegree = 1 at forwardLinear
  have degreeProjected := congrArg Hom.frobeniusDegree forwardComp
  change forward.frobeniusDegree * 1 = arrow.frobeniusDegree at degreeProjected
  rw [forwardLinear] at degreeProjected
  have arrowLinear : arrow.frobeniusDegree = 1 := by
    simpa using degreeProjected.symm
  have divisorProjected := congrArg Hom.divisor forwardComp
  change Phi.pullback forward.base 0 + 1 • forward.divisor =
    arrow.divisor at divisorProjected
  have forwardIsometric := forwardType.2
  change forward.divisor = 0 at forwardIsometric
  rw [forwardIsometric] at divisorProjected
  have arrowIsometric : arrow.divisor = 0 := by
    simpa using divisorProjected.symm
  exact ⟨arrowLinear, isCoAngular Phi data arrow, arrowIsometric⟩

end
end Iut.SourceModelFrobenioid.Carrier
