import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralUnitKummer

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

/-!
  The canonical local integral-unit Kummer map.

  This module proves the root-choice and multiplication obligations left open
  by `LocalIntegralUnitKummer`.  Quotients of two compatible root systems give
  an actual integral-unit cyclotome.  The two resulting Galois cocycles differ
  by its explicit coboundary, so their continuous `H^1` germs agree.  Product
  root systems then make the canonical germs into a genuine monoid homomorphism.

  The argument follows the corresponding construction in
  `promachina/iut-lean`, `Iut/Foundations/SourceThetaEvaluation.lean`, at
  audited commit `2eb61e1b037635a5346f7265f520b458155303ed` (Apache-2.0),
  specialized to this project's literal local monoid.
-/

namespace LeanFormal.IUT

namespace LocalMLFModelTMPair

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The integral-unit quotient of two compatible root systems for one local
monoid value. -/
structure IntegralCompatibleRootComparison
    (value : LocalIntegralMonoid p)
    (first second : CompatibleRootSystem
      (LocalGroupification p) (Algebra.GrothendieckGroup.of value)) where
  comparisonUnit : ℚ → (LocalIntegralMonoid p)ˣ
  comparison_spec : ∀ q : ℚ,
    unitGrothendieckHom p (comparisonUnit q) =
      (second.roots q).toMul / (first.roots q).toMul

namespace IntegralCompatibleRootComparison

variable
  {p : Nat} [Fact (Nat.Prime p)]
  {value : LocalIntegralMonoid p}
  {first second : CompatibleRootSystem
    (LocalGroupification p) (Algebra.GrothendieckGroup.of value)}

noncomputable def ofRoots
    (value : LocalIntegralMonoid p)
    (first second : CompatibleRootSystem
      (LocalGroupification p) (Algebra.GrothendieckGroup.of value)) :
    IntegralCompatibleRootComparison p value first second where
  comparisonUnit q := Classical.choose
    (quotientUnit_exists p value first second q)
  comparison_spec q := Classical.choose_spec
    (quotientUnit_exists p value first second q)

theorem comparisonUnit_zero
    (comparison : IntegralCompatibleRootComparison p value first second) :
    comparison.comparisonUnit 0 = 1 := by
  apply unitGrothendieckHom_injective p
  rw [comparison.comparison_spec]
  have first_zero := congrArg Additive.toMul first.roots.map_zero
  have second_zero := congrArg Additive.toMul second.roots.map_zero
  change (first.roots 0).toMul = 1 at first_zero
  change (second.roots 0).toMul = 1 at second_zero
  rw [first_zero, second_zero, div_one, map_one]

theorem comparisonUnit_add
    (comparison : IntegralCompatibleRootComparison p value first second)
    (q r : ℚ) :
    comparison.comparisonUnit (q + r) =
      comparison.comparisonUnit q * comparison.comparisonUnit r := by
  apply unitGrothendieckHom_injective p
  rw [map_mul, comparison.comparison_spec, comparison.comparison_spec,
    comparison.comparison_spec]
  have first_add := congrArg Additive.toMul (first.roots.map_add q r)
  have second_add := congrArg Additive.toMul (second.roots.map_add q r)
  change
    (first.roots (q + r)).toMul =
      (first.roots q).toMul * (first.roots r).toMul at first_add
  change
    (second.roots (q + r)).toMul =
      (second.roots q).toMul * (second.roots r).toMul at second_add
  rw [first_add, second_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

noncomputable def comparisonAddHom
    (comparison : IntegralCompatibleRootComparison p value first second) :
    ℚ →+ Additive (LocalIntegralMonoid p)ˣ where
  toFun q := Additive.ofMul (comparison.comparisonUnit q)
  map_zero' := congrArg Additive.ofMul comparison.comparisonUnit_zero
  map_add' q r := congrArg Additive.ofMul
    (comparison.comparisonUnit_add q r)

theorem comparisonUnit_one
    (comparison : IntegralCompatibleRootComparison p value first second) :
    comparison.comparisonUnit 1 = 1 := by
  apply unitGrothendieckHom_injective p
  rw [comparison.comparison_spec]
  have first_one := congrArg Additive.toMul first.root_one
  have second_one := congrArg Additive.toMul second.root_one
  change
    (first.roots 1).toMul = Algebra.GrothendieckGroup.of value at first_one
  change
    (second.roots 1).toMul = Algebra.GrothendieckGroup.of value at second_one
  rw [first_one, second_one, map_one]
  simp

theorem zmultiples_le_comparisonAddHom_ker
    (comparison : IntegralCompatibleRootComparison p value first second) :
    AddSubgroup.zmultiples (1 : ℚ) ≤ comparison.comparisonAddHom.ker := by
  rw [AddSubgroup.zmultiples_le]
  change comparison.comparisonAddHom 1 = 0
  apply Additive.toMul.injective
  exact comparison.comparisonUnit_one

/-- The quotient of two compatible roots as an actual element of `mu_Z(M)`. -/
noncomputable def cyclotome
    (comparison : IntegralCompatibleRootComparison p value first second) :
    KummerCyclotome (LocalIntegralMonoid p)ˣ :=
  AddMonoidHom.toMultiplicativeLeft
    (QuotientAddGroup.lift
      (AddSubgroup.zmultiples (1 : ℚ))
      comparison.comparisonAddHom
      comparison.zmultiples_le_comparisonAddHom_ker)

@[simp]
theorem cyclotome_mk
    (comparison : IntegralCompatibleRootComparison p value first second)
    (q : ℚ) :
    comparison.cyclotome
        (Multiplicative.ofAdd (q : AddCircle (1 : ℚ))) =
      comparison.comparisonUnit q :=
  rfl

end IntegralCompatibleRootComparison

namespace IntegralKummerRootRealization

variable
  {p : Nat} [Fact (Nat.Prime p)]
  {pair : LocalMLFModelTMPair p}
  {firstSubgroup secondSubgroup : OpenSubgroup pair.actingGroup}
  {value firstValue secondValue : LocalIntegralMonoid p}

/-- Changing compatible roots changes the integral root-ratio cocycle by the
explicit coboundary of their quotient. -/
theorem ratioUnit_relation
    (first : IntegralKummerRootRealization
      p pair firstSubgroup value)
    (second : IntegralKummerRootRealization
      p pair secondSubgroup value)
    (comparison : IntegralCompatibleRootComparison p value
      first.rootSystem second.rootSystem)
    (g : (firstSubgroup ⊓ secondSubgroup :
      OpenSubgroup pair.actingGroup)) (q : ℚ) :
    second.ratioUnit ⟨(g : pair.actingGroup), g.property.2⟩ q =
      (comparison.comparisonUnit q)⁻¹ *
        first.ratioUnit ⟨(g : pair.actingGroup), g.property.1⟩ q *
          Units.map (pair.action p (g : pair.actingGroup)).toMonoidHom
            (comparison.comparisonUnit q) := by
  apply unitGrothendieckHom_injective p
  rw [map_mul, map_mul, map_inv, second.ratio_spec, first.ratio_spec,
    ← pair.unitGrothendieckHom_action p, comparison.comparison_spec]
  let firstRoot := (first.rootSystem.roots q).toMul
  let secondRoot := (second.rootSystem.roots q).toMul
  let firstImage :=
    pair.groupificationAction p (g : pair.actingGroup) firstRoot
  let secondImage :=
    pair.groupificationAction p (g : pair.actingGroup) secondRoot
  change
    secondImage / secondRoot =
      (secondRoot / firstRoot)⁻¹ *
          (firstImage / firstRoot) *
        pair.groupificationAction p (g : pair.actingGroup)
          (secondRoot / firstRoot)
  rw [map_div (pair.groupificationAction p (g : pair.actingGroup))]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  change
    secondImage * secondRoot⁻¹ =
      (firstRoot * secondRoot⁻¹) *
          (firstImage * firstRoot⁻¹) *
        (secondImage * firstImage⁻¹)
  calc
    secondImage * secondRoot⁻¹ =
        (firstRoot * firstRoot⁻¹) *
          (firstImage * firstImage⁻¹) *
          (secondImage * secondRoot⁻¹) := by simp
    _ = _ := by ac_rfl

theorem ratioCyclotome_relation
    (first : IntegralKummerRootRealization
      p pair firstSubgroup value)
    (second : IntegralKummerRootRealization
      p pair secondSubgroup value)
    (comparison : IntegralCompatibleRootComparison p value
      first.rootSystem second.rootSystem)
    (g : (firstSubgroup ⊓ secondSubgroup :
      OpenSubgroup pair.actingGroup)) :
    second.ratioCyclotome
        ⟨(g : pair.actingGroup), g.property.2⟩ =
      comparison.cyclotome⁻¹ *
        first.ratioCyclotome
            ⟨(g : pair.actingGroup), g.property.1⟩ *
          (KummerCyclotome.continuousAction
            (pair.discreteIntegralUnitAction p)).act
            (g : pair.actingGroup) comparison.cyclotome := by
  apply MonoidHom.ext
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    second.ratioCyclotome
          ⟨(g : pair.actingGroup), g.property.2⟩
          (Multiplicative.ofAdd additiveCircle) =
      (comparison.cyclotome⁻¹ *
          first.ratioCyclotome
              ⟨(g : pair.actingGroup), g.property.1⟩ *
        (KummerCyclotome.continuousAction
          (pair.discreteIntegralUnitAction p)).act
          (g : pair.actingGroup) comparison.cyclotome)
        (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q => exact first.ratioUnit_relation second comparison g q

theorem representatives_equivalent
    (first : IntegralKummerRootRealization
      p pair firstSubgroup value)
    (second : IntegralKummerRootRealization
      p pair secondSubgroup value)
    (comparison : IntegralCompatibleRootComparison p value
      first.rootSystem second.rootSystem) :
    first.representative.Equivalent second.representative := by
  refine
    ⟨firstSubgroup ⊓ secondSubgroup, inf_le_left, inf_le_right,
      comparison.cyclotome, ?_⟩
  intro g
  exact first.ratioCyclotome_relation second comparison g

theorem germ_eq
    (first : IntegralKummerRootRealization
      p pair firstSubgroup value)
    (second : IntegralKummerRootRealization
      p pair secondSubgroup value) :
    first.germ = second.germ := by
  apply Quotient.sound
  exact first.representatives_equivalent second
    (IntegralCompatibleRootComparison.ofRoots
      value first.rootSystem second.rootSystem)

set_option maxHeartbeats 800000 in
-- The nested Grothendieck action and root-system structure elaborate together.
set_option synthInstance.maxHeartbeats 100000 in
/-- Multiply two integral root realizations after restricting to the
intersection of their open subgroups. -/
noncomputable def mul
    (first : IntegralKummerRootRealization
      p pair firstSubgroup firstValue)
    (second : IntegralKummerRootRealization
      p pair secondSubgroup secondValue) :
    IntegralKummerRootRealization p pair
      (firstSubgroup ⊓ secondSubgroup) (firstValue * secondValue) where
  fixed g := by
    rw [map_mul, first.fixed ⟨g, g.property.1⟩,
      second.fixed ⟨g, g.property.2⟩]
  rootSystem :=
    { roots := first.rootSystem.roots + second.rootSystem.roots
      root_one := by
        apply Additive.toMul.injective
        change
          (first.rootSystem.roots 1).toMul *
              (second.rootSystem.roots 1).toMul =
            Algebra.GrothendieckGroup.of (firstValue * secondValue)
        have first_one := congrArg Additive.toMul first.rootSystem.root_one
        have second_one := congrArg Additive.toMul second.rootSystem.root_one
        change
          (first.rootSystem.roots 1).toMul =
            Algebra.GrothendieckGroup.of firstValue at first_one
        change
          (second.rootSystem.roots 1).toMul =
            Algebra.GrothendieckGroup.of secondValue at second_one
        rw [first_one, second_one, map_mul] }
  ratioUnit g q :=
    first.ratioUnit ⟨(g : pair.actingGroup), g.property.1⟩ q *
      second.ratioUnit ⟨(g : pair.actingGroup), g.property.2⟩ q
  ratio_spec g q := by
    rw [map_mul, first.ratio_spec, second.ratio_spec]
    change
      (pair.groupificationAction p (g : pair.actingGroup)
            (first.rootSystem.roots q).toMul /
          (first.rootSystem.roots q).toMul) *
          (pair.groupificationAction p (g : pair.actingGroup)
              (second.rootSystem.roots q).toMul /
            (second.rootSystem.roots q).toMul) =
        pair.groupificationAction p (g : pair.actingGroup)
            ((first.rootSystem.roots q).toMul *
              (second.rootSystem.roots q).toMul) /
          ((first.rootSystem.roots q).toMul *
            (second.rootSystem.roots q).toMul)
    rw [map_mul (pair.groupificationAction p (g : pair.actingGroup))]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl

theorem mul_germ
    (first : IntegralKummerRootRealization
      p pair firstSubgroup firstValue)
    (second : IntegralKummerRootRealization
      p pair secondSubgroup secondValue) :
    (first.mul second).germ = first.germ * second.germ := by
  apply Quotient.sound
  refine Iut.ContinuousH1GermRepresentative.Equivalent.of_equal_on
    (firstSubgroup ⊓ secondSubgroup) le_rfl le_rfl ?_
  intro g
  apply MonoidHom.ext
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    (first.ratioCyclotome
        ⟨(g : pair.actingGroup), g.property.1⟩ *
      second.ratioCyclotome
        ⟨(g : pair.actingGroup), g.property.2⟩)
        (Multiplicative.ofAdd additiveCircle) =
      (first.mul second).ratioCyclotome g
        (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q => rfl

end IntegralKummerRootRealization

/-- The canonical local unit Kummer germ, now independent of compatible-root
choices by the preceding coboundary theorem. -/
noncomputable def integralUnitKummerGerm
    (pair : LocalMLFModelTMPair p) (unit : (LocalIntegralMonoid p)ˣ) :
    Iut.ContinuousH1Germ
      (KummerCyclotome.continuousAction
        (pair.discreteIntegralUnitAction p)) :=
  (pair.canonicalIntegralKummerRootRealization p
    (unit : LocalIntegralMonoid p)).germ

theorem integralUnitKummerGerm_mul
    (pair : LocalMLFModelTMPair p)
    (first second : (LocalIntegralMonoid p)ˣ) :
    pair.integralUnitKummerGerm p (first * second) =
      pair.integralUnitKummerGerm p first *
        pair.integralUnitKummerGerm p second := by
  let firstRealization := pair.canonicalIntegralKummerRootRealization p
    (first : LocalIntegralMonoid p)
  let secondRealization := pair.canonicalIntegralKummerRootRealization p
    (second : LocalIntegralMonoid p)
  let productRealization := firstRealization.mul secondRealization
  let canonicalProduct := pair.canonicalIntegralKummerRootRealization p
    ((first * second : (LocalIntegralMonoid p)ˣ) : LocalIntegralMonoid p)
  calc
    pair.integralUnitKummerGerm p (first * second) =
        productRealization.germ :=
      canonicalProduct.germ_eq productRealization
    _ = pair.integralUnitKummerGerm p first *
          pair.integralUnitKummerGerm p second :=
      firstRealization.mul_germ secondRealization

theorem integralUnitKummerGerm_one
    (pair : LocalMLFModelTMPair p) :
    pair.integralUnitKummerGerm p 1 = 1 := by
  have productIdentity :=
    pair.integralUnitKummerGerm_mul p 1 1
  have idempotent :
      pair.integralUnitKummerGerm p 1 =
        pair.integralUnitKummerGerm p 1 *
          pair.integralUnitKummerGerm p 1 := by
    simpa only [one_mul] using productIdentity
  have cancellable :
      pair.integralUnitKummerGerm p 1 * 1 =
        pair.integralUnitKummerGerm p 1 *
          pair.integralUnitKummerGerm p 1 := by
    simpa only [mul_one] using idempotent
  exact (mul_left_cancel cancellable).symm

/-- The actual integral-unit-valued local Kummer homomorphism. -/
noncomputable def integralUnitKummerHom
    (pair : LocalMLFModelTMPair p) :
    (LocalIntegralMonoid p)ˣ →*
      Iut.ContinuousH1Germ
        (KummerCyclotome.continuousAction
          (pair.discreteIntegralUnitAction p)) where
  toFun := pair.integralUnitKummerGerm p
  map_one' := pair.integralUnitKummerGerm_one p
  map_mul' := pair.integralUnitKummerGerm_mul p

@[simp]
theorem integralUnitKummerHom_apply
    (pair : LocalMLFModelTMPair p) (unit : (LocalIntegralMonoid p)ˣ) :
    pair.integralUnitKummerHom p unit =
      pair.integralUnitKummerGerm p unit :=
  rfl

end LocalMLFModelTMPair

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localIntegralUnitKummerMap : Obligation :=
  { id := "IUT-II.local-integral-unit-Kummer-map"
    source := "Absolute Anabelian Topics III, Proposition 3.2(ii); Proposition 3.3(i) input"
    status := VerificationStatus.proved
    note :=
      "Lean constructs the integral-unit quotient of any two compatible root " ++
        "systems and proves the associated cocycles differ by its explicit " ++
        "coboundary. Product root realizations then prove that the canonical " ++
        "unit-valued H1 germs form a genuine monoid homomorphism. Its literal " ++
        "mono-analytic specialization is proved injective in the following " ++
        "module; Frobenioid-side evaluation remains a separate obligation."
    dependsOn := [ "IUT-II.local-integral-unit-Kummer-realization" ] }

end LeanFormal.IUT.Audit
