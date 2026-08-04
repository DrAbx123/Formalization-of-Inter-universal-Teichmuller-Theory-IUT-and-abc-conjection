import LeanFormal.IUT.IUTII.Frobenioid.LocalUnitKummerMap
import LeanFormal.IUT.IUTII.Kummer.LocalFieldRigidity
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Quotient

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

/-!
  Injectivity of the actual mono-analytic integral-unit Kummer map.

  The finite-quotient and fixed-field argument is adapted from
  `promachina/iut-lean`, `SourceMLFKummerFaithfulness.lean` and
  `SourceThetaEvaluation.lean`, at audited commit
  `2eb61e1b037635a5346f7265f520b458155303ed` (Apache-2.0).  It is specialized
  to `Q_p`, its algebraic closure, and the literal local integral monoid.

  Equality of a Kummer germ with one supplies an explicit coboundary on a
  common open subgroup.  Adjusting every compatible rational root by that
  coboundary gives roots of all positive degrees fixed by the same subgroup.
  They lie in one finite fixed field.  Its integral-closure unit group is
  residually finite, so an element divisible in every positive degree is one.
-/

namespace LeanFormal.IUT

namespace LocalMLFModelTMPair

variable (p : Nat) [Fact (Nat.Prime p)]

/-- A trivial canonical Kummer germ gives roots of every positive degree fixed
by one common open subgroup. -/
theorem fixed_roots_of_integralUnitKummer_eq_one
    (pair : LocalMLFModelTMPair p)
    (value : (LocalIntegralMonoid p)ˣ)
    (hvalue : pair.integralUnitKummerHom p value = 1) :
    ∃ subgroup : OpenSubgroup pair.actingGroup,
      ∀ n : ℕ, 0 < n →
        ∃ root : LocalGroupification p,
          root ^ n = unitGrothendieckHom p value ∧
          ∀ g : subgroup,
            pair.groupificationAction p (g : pair.actingGroup) root = root := by
  let realization := pair.canonicalIntegralKummerRootRealization p
    (value : LocalIntegralMonoid p)
  have germ_eq_one : realization.germ = 1 := by
    simpa [integralUnitKummerHom, integralUnitKummerGerm] using hvalue
  have equivalent :
      realization.representative.Equivalent
        (Iut.ContinuousH1GermRepresentative.one
          (action := KummerCyclotome.continuousAction
            (pair.discreteIntegralUnitAction p))) :=
    Quotient.exact germ_eq_one
  rcases equivalent with
    ⟨subgroup, hRealization, _hOne, cochain, equivalent⟩
  refine ⟨subgroup, ?_⟩
  intro n hn
  let q : ℚ := (n : ℚ)⁻¹
  let circle : Multiplicative (AddCircle (1 : ℚ)) :=
    Multiplicative.ofAdd (q : AddCircle (1 : ℚ))
  let cochainUnit : (LocalIntegralMonoid p)ˣ := cochain circle
  let root : LocalGroupification p :=
    (realization.rootSystem.roots q).toMul *
      unitGrothendieckHom p cochainUnit
  refine ⟨root, ?_, ?_⟩
  · have q_multiple : n • q = (1 : ℚ) := by
      dsimp [q]
      rw [nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')
    have root_power := congrArg Additive.toMul
      (realization.rootSystem.roots.map_nsmul n q)
    change
      (realization.rootSystem.roots (n • q)).toMul =
        (realization.rootSystem.roots q).toMul ^ n at root_power
    have root_power_value :
        (realization.rootSystem.roots q).toMul ^ n =
          unitGrothendieckHom p value := by
      rw [← root_power, q_multiple, realization.rootSystem.root_one]
      rfl
    have circle_power : circle ^ n = 1 := by
      apply Multiplicative.toAdd.injective
      change n • (q : AddCircle (1 : ℚ)) = 0
      change ((n • q : ℚ) : AddCircle (1 : ℚ)) = 0
      rw [q_multiple]
      exact AddCircle.coe_period (p := (1 : ℚ))
    have cochain_power : cochainUnit ^ n = 1 := by
      change (cochain circle) ^ n = 1
      rw [← map_pow, circle_power, map_one]
    dsimp [root]
    rw [mul_pow, root_power_value, ← map_pow, cochain_power,
      map_one, mul_one]
  · intro g
    let realizationG : realization.representative.subgroup :=
      ⟨(g : pair.actingGroup), hRealization g.property⟩
    have cohomology := equivalent g
    change
      (1 : KummerCyclotome (LocalIntegralMonoid p)ˣ) =
        cochain⁻¹ * realization.ratioCyclotome realizationG *
          (KummerCyclotome.continuousAction
            (pair.discreteIntegralUnitAction p)).act
            (g : pair.actingGroup) cochain at cohomology
    have coordinate := congrArg (fun cyclotome => cyclotome circle) cohomology
    change
      1 = cochainUnit⁻¹ * realization.ratioUnit realizationG q *
        Units.map (pair.action p (g : pair.actingGroup)).toMonoidHom
          cochainUnit at coordinate
    have ratio_eq :
        realization.ratioUnit realizationG q =
          cochainUnit *
            (Units.map
              (pair.action p (g : pair.actingGroup)).toMonoidHom
              cochainUnit)⁻¹ := by
      have transformed := congrArg
        (fun x => cochainUnit * x *
          (Units.map
            (pair.action p (g : pair.actingGroup)).toMonoidHom
            cochainUnit)⁻¹)
        coordinate
      simpa [mul_assoc] using transformed.symm
    dsimp [root]
    change
      pair.groupificationActionHom p (g : pair.actingGroup)
          ((realization.rootSystem.roots q).toMul *
            unitGrothendieckHom p cochainUnit) =
        (realization.rootSystem.roots q).toMul *
          unitGrothendieckHom p cochainUnit
    rw [map_mul (pair.groupificationActionHom p (g : pair.actingGroup))]
    have cochain_action :=
      pair.groupificationActionMulAut_of p
        (g : pair.actingGroup) cochainUnit
    change
      pair.groupificationActionHom p (g : pair.actingGroup)
          (unitGrothendieckHom p cochainUnit) =
        unitGrothendieckHom p
          (Units.map (pair.action p (g : pair.actingGroup)).toMonoidHom
            cochainUnit) at cochain_action
    rw [cochain_action]
    have ratio_spec := realization.ratio_spec realizationG q
    rw [ratio_eq] at ratio_spec
    change
      unitGrothendieckHom p
          (cochainUnit *
            (Units.map
              (pair.action p (g : pair.actingGroup)).toMonoidHom
              cochainUnit)⁻¹) =
        pair.groupificationActionHom p (g : pair.actingGroup)
            (realization.rootSystem.roots q).toMul /
          (realization.rootSystem.roots q).toMul at ratio_spec
    have acted_root :
        pair.groupificationActionHom p (g : pair.actingGroup)
            (realization.rootSystem.roots q).toMul =
          (unitGrothendieckHom p cochainUnit *
              (unitGrothendieckHom p
                (Units.map
                  (pair.action p (g : pair.actingGroup)).toMonoidHom
                  cochainUnit))⁻¹) *
            (realization.rootSystem.roots q).toMul := by
      rw [map_mul, map_inv] at ratio_spec
      calc
        _ =
            (pair.groupificationActionHom p (g : pair.actingGroup)
                (realization.rootSystem.roots q).toMul /
              (realization.rootSystem.roots q).toMul) *
              (realization.rootSystem.roots q).toMul := by simp
        _ = _ := by rw [← ratio_spec]
    rw [acted_root]
    let cochainImage := unitGrothendieckHom p cochainUnit
    let actedCochainImage := unitGrothendieckHom p
      (Units.map (pair.action p (g : pair.actingGroup)).toMonoidHom
        cochainUnit)
    let sourceRoot := (realization.rootSystem.roots q).toMul
    change
      ((cochainImage * actedCochainImage⁻¹) * sourceRoot) *
          actedCochainImage =
        sourceRoot * cochainImage
    calc
      _ = cochainImage *
            (actedCochainImage⁻¹ * actedCochainImage) * sourceRoot := by
          ac_rfl
      _ = cochainImage * sourceRoot := by rw [inv_mul_cancel, mul_one]
      _ = _ := mul_comm _ _

end LocalMLFModelTMPair

namespace LocalIntegralUnitKummerInjectivity

universe u

open ValuativeRel

set_option maxHeartbeats 800000 in
-- Quotient-module finiteness synthesis traverses the scalar tower.
theorem finite_quotient_map
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (S ⧸ I.map (algebraMap R S)) := by
  let J := I.map (algebraMap R S)
  let B := R ⧸ J.comap (algebraMap R S)
  let T := S ⧸ J
  let factor : R ⧸ I →+* B :=
    Ideal.Quotient.factor Ideal.le_comap_map
  letI : Finite B := Finite.of_surjective factor
    (Ideal.Quotient.factor_surjective _)
  letI : Algebra B T := inferInstance
  letI : IsScalarTower R B T :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
  letI : Module.Finite R T := Module.Finite.quotient R J
  letI : Module.Finite B T :=
    Module.Finite.of_restrictScalars_finite R B T
  exact Module.finite_of_finite B

set_option maxHeartbeats 800000 in
-- Krull intersection and the finite quotient construction elaborate together.
theorem units_residuallyFinite_of_finite_quotients
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤)
    (finiteQuotient : ∀ n : ℕ, Finite (R ⧸ I ^ n)) :
    Group.ResiduallyFinite Sˣ := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro unit unit_ne_one
  have value_sub_one_ne_zero : (unit : S) - 1 ≠ 0 := by
    intro equality
    apply unit_ne_one
    apply Units.ext
    exact sub_eq_zero.mp equality
  have exists_separating_power :
      ∃ n : ℕ, (unit : S) - 1 ∉
        (I ^ n • (⊤ : Submodule R S)) := by
    by_contra no_power
    push Not at no_power
    have in_intersection :
        (unit : S) - 1 ∈
          (⨅ n : ℕ, I ^ n • (⊤ : Submodule R S)) :=
      (Submodule.mem_iInf _).mpr no_power
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hI] at in_intersection
    exact value_sub_one_ne_zero ((Submodule.mem_bot R).mp in_intersection)
  obtain ⟨n, separating⟩ := exists_separating_power
  let J : Ideal S := (I ^ n).map (algebraMap R S)
  have separating_ideal : (unit : S) - 1 ∉ J := by
    intro member
    apply separating
    rw [Ideal.smul_top_eq_map]
    exact member
  letI : Finite (R ⧸ I ^ n) := finiteQuotient n
  letI : Finite (S ⧸ J) := finite_quotient_map R S (I ^ n)
  let reduction : Sˣ →* (S ⧸ J)ˣ := Units.map (Ideal.Quotient.mk J)
  refine ⟨(S ⧸ J)ˣ, inferInstance, inferInstance, reduction, ?_⟩
  intro reduction_eq_one
  apply separating_ideal
  apply (Ideal.Quotient.mk_eq_one_iff_sub_mem (unit : S)).mp
  exact congrArg Units.val reduction_eq_one

set_option maxHeartbeats 800000 in
-- Integral-closure finiteness and DVR quotient instances synthesize together.
theorem integralClosureUnits_residuallyFinite
    (K : Type u) [Field K] [ValuativeRel K]
    [CharZero K]
    [IsDiscreteValuationRing
      (Valuation.integer (ValuativeRel.valuation K))]
    [Finite
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation K)))]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] :
    Group.ResiduallyFinite
      (integralClosure (Valuation.integer (ValuativeRel.valuation K)) L)ˣ := by
  let R := Valuation.integer (ValuativeRel.valuation K)
  let S := integralClosure R L
  letI : IsFractionRing R K := inferInstance
  letI : Module.Finite R S := IsIntegralClosure.finite R K L S
  apply units_residuallyFinite_of_finite_quotients
    R S (IsLocalRing.maximalIdeal R)
  · exact Ideal.IsPrime.ne_top'
  · intro n
    exact (IsLocalRing.finite_quotient_iff).mpr ⟨n, le_rfl⟩

variable (p : Nat) [Fact (Nat.Prime p)]

theorem padicMulValuation_le_one_iff_norm_le_one (x : ℚ_[p]) :
    Padic.mulValuation x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  rw [Padic.norm_le_one_iff_val_nonneg]
  change (if x = 0 then 0 else WithZero.exp (-x.valuation)) ≤ 1 ↔ _
  rw [if_neg hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

/-- The canonical valuation ring attached to Mathlib's valuative relation on
`Q_p` is the usual ring of `p`-adic integers. -/
noncomputable def padicCanonicalIntegerEquiv :
    Valuation.integer (ValuativeRel.valuation ℚ_[p]) ≃+* ℤ_[p] where
  toFun x := ⟨x, by
    apply (padicMulValuation_le_one_iff_norm_le_one p x).mp
    apply ((Padic.mulValuation (p := p)).vle_one_iff).mp
    apply ((ValuativeRel.valuation ℚ_[p]).vle_one_iff).mpr
    exact x.property⟩
  invFun x := ⟨x, by
    have hx : Padic.mulValuation (x : ℚ_[p]) ≤ 1 :=
      (padicMulValuation_le_one_iff_norm_le_one p x.1).mpr x.property
    apply ((ValuativeRel.valuation ℚ_[p]).vle_one_iff).mp
    apply ((Padic.mulValuation (p := p)).vle_one_iff).mpr
    exact hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

noncomputable instance padicCanonicalIntegerDVR :
    IsDiscreteValuationRing
      (Valuation.integer (ValuativeRel.valuation ℚ_[p])) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (padicCanonicalIntegerEquiv p).symm

noncomputable instance padicCanonicalIntegerFiniteResidue :
    Finite
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation ℚ_[p]))) := by
  letI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p)
      (PadicInt.residueField (p := p)).symm.toEquiv
  exact Finite.of_equiv
    (IsLocalRing.ResidueField ℤ_[p])
    (IsLocalRing.ResidueField.mapEquiv
      (padicCanonicalIntegerEquiv p)).symm.toEquiv

noncomputable def FixedField
    (subgroup : OpenSubgroup (LocalAbsoluteGalois p)) :
    IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
  IntermediateField.fixedField subgroup.toSubgroup

theorem fixedField_finiteDimensional
    (subgroup : OpenSubgroup (LocalAbsoluteGalois p)) :
    FiniteDimensional ℚ_[p] (FixedField p subgroup) := by
  let closedSubgroup : ClosedSubgroup (LocalAbsoluteGalois p) :=
    { toSubgroup := subgroup.toSubgroup
      isClosed' := subgroup.isClosed }
  apply
    (InfiniteGalois.isOpen_iff_finite
      (IntermediateField.fixedField subgroup.toSubgroup)).mp
  change IsOpen
    ((IntermediateField.fixedField
      closedSubgroup.toSubgroup).fixingSubgroup.carrier)
  rw [InfiniteGalois.fixingSubgroup_fixedField closedSubgroup]
  exact subgroup.isOpen

noncomputable def fixedFieldIntegralUnit
    (subgroup : OpenSubgroup (LocalAbsoluteGalois p))
    (fieldUnit : (AlgebraicClosure ℚ_[p])ˣ)
    (fixed : ∀ sigma : LocalAbsoluteGalois p,
      sigma ∈ subgroup →
        localGaloisUnitsAction p sigma fieldUnit = fieldUnit)
    (integral : IsIntegral
      (Valuation.integer (ValuativeRel.valuation ℚ_[p]))
      (fieldUnit : AlgebraicClosure ℚ_[p]))
    (inverseIntegral : IsIntegral
      (Valuation.integer (ValuativeRel.valuation ℚ_[p]))
      (fieldUnit⁻¹ : AlgebraicClosure ℚ_[p])) :
    (integralClosure
      (Valuation.integer (ValuativeRel.valuation ℚ_[p]))
      (FixedField p subgroup))ˣ := by
  let fixedField := FixedField p subgroup
  let baseRing := Valuation.integer (ValuativeRel.valuation ℚ_[p])
  have fieldUnit_mem :
      (fieldUnit : AlgebraicClosure ℚ_[p]) ∈ fixedField := by
    change
      (fieldUnit : AlgebraicClosure ℚ_[p]) ∈
        IntermediateField.fixedField subgroup.toSubgroup
    rw [IntermediateField.mem_fixedField_iff]
    intro sigma hsigma
    exact congrArg Units.val (fixed sigma hsigma)
  have fieldUnit_inv_mem :
      (fieldUnit⁻¹ : AlgebraicClosure ℚ_[p]) ∈ fixedField := by
    change
      (fieldUnit⁻¹ : AlgebraicClosure ℚ_[p]) ∈
        IntermediateField.fixedField subgroup.toSubgroup
    rw [IntermediateField.mem_fixedField_iff]
    intro sigma hsigma
    have fieldUnit_fixed :
        sigma (fieldUnit : AlgebraicClosure ℚ_[p]) = fieldUnit := by
      change
        ((localGaloisUnitsAction p sigma fieldUnit :
            (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) =
          (fieldUnit : AlgebraicClosure ℚ_[p])
      exact congrArg Units.val (fixed sigma hsigma)
    rw [map_inv₀ sigma, fieldUnit_fixed]
  let fixedValue : fixedField := ⟨fieldUnit, fieldUnit_mem⟩
  let fixedInverse : fixedField := ⟨fieldUnit⁻¹, fieldUnit_inv_mem⟩
  have fixedValue_integral : IsIntegral baseRing fixedValue :=
    IntermediateField.coe_isIntegral_iff.mp integral
  have fixedInverse_integral : IsIntegral baseRing fixedInverse :=
    IntermediateField.coe_isIntegral_iff.mp inverseIntegral
  let integralValue : integralClosure baseRing fixedField :=
    ⟨fixedValue, fixedValue_integral⟩
  let integralInverse : integralClosure baseRing fixedField :=
    ⟨fixedInverse, fixedInverse_integral⟩
  exact
    { val := integralValue
      inv := integralInverse
      val_inv := by
        apply Subtype.ext
        apply Subtype.ext
        change (fieldUnit : AlgebraicClosure ℚ_[p]) *
            (fieldUnit⁻¹ : AlgebraicClosure ℚ_[p]) = 1
        exact mul_inv_cancel₀ fieldUnit.ne_zero
      inv_val := by
        apply Subtype.ext
        apply Subtype.ext
        change (fieldUnit⁻¹ : AlgebraicClosure ℚ_[p]) *
            (fieldUnit : AlgebraicClosure ℚ_[p]) = 1
        exact inv_mul_cancel₀ fieldUnit.ne_zero }

theorem monoAnalytic_unit_eq_one_of_Kummer_eq_one
    (value : (LocalIntegralMonoid p)ˣ)
    (hvalue : (LocalMLFModelTMPair.monoAnalytic p).integralUnitKummerHom p
      value = 1) :
    value = 1 := by
  let pair := LocalMLFModelTMPair.monoAnalytic p
  obtain ⟨subgroup, fixedRoots⟩ :=
    pair.fixed_roots_of_integralUnitKummer_eq_one p value hvalue
  let fixedField := FixedField p subgroup
  let baseRing := Valuation.integer (ValuativeRel.valuation ℚ_[p])
  let fieldEquiv :=
    LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p
  let fieldValue : (AlgebraicClosure ℚ_[p])ˣ :=
    fieldEquiv (LocalMLFModelTMPair.unitGrothendieckHom p value)
  have fieldValue_eq :
      fieldValue = LocalIntegralMonoid.unitEvaluation p value := by
    exact LocalMLFModelTMPair.groupificationEquiv_unitGrothendieckHom p value
  have fieldValue_integral :
      IsIntegral baseRing (fieldValue : AlgebraicClosure ℚ_[p]) := by
    rw [fieldValue_eq]
    exact value.val.1.property
  have fieldValue_inverse_integral :
      IsIntegral baseRing (fieldValue⁻¹ : AlgebraicClosure ℚ_[p]) := by
    rw [fieldValue_eq]
    have inverse_eq :
        (value.inv.1.1 : AlgebraicClosure ℚ_[p]) =
          (value.val.1.1 : AlgebraicClosure ℚ_[p])⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have inverseProduct := congrArg
        (fun sourceValue : LocalIntegralMonoid p =>
          (sourceValue.1.1 : AlgebraicClosure ℚ_[p])) value.inv_val
      exact inverseProduct
    change IsIntegral baseRing
      ((value.val.1.1 : AlgebraicClosure ℚ_[p])⁻¹)
    rw [← inverse_eq]
    exact value.inv.1.property
  obtain ⟨firstRoot, firstRootPower, firstRootFixed⟩ :=
    fixedRoots 1 one_pos
  have fieldValue_fixed :
      ∀ sigma : LocalAbsoluteGalois p, sigma ∈ subgroup →
        localGaloisUnitsAction p sigma fieldValue = fieldValue := by
    intro sigma hsigma
    have fieldRootAction :=
      pair.groupificationEquivAlgebraicClosureUnits_action p sigma firstRoot
    have augmentation_sigma : pair.augmentation sigma = sigma := rfl
    rw [augmentation_sigma] at fieldRootAction
    have fixedRoot := firstRootFixed ⟨sigma, hsigma⟩
    have fieldRoot_eq : fieldEquiv firstRoot = fieldValue := by
      dsimp [fieldValue]
      rw [← firstRootPower, pow_one]
    rw [← fieldRoot_eq, ← fieldRootAction, fixedRoot]
  let integralValue := fixedFieldIntegralUnit p subgroup fieldValue
    fieldValue_fixed fieldValue_integral fieldValue_inverse_integral
  have integralValue_image :
      (((integralValue : integralClosure baseRing fixedField) : fixedField) :
          AlgebraicClosure ℚ_[p]) =
        (fieldValue : AlgebraicClosure ℚ_[p]) := rfl
  have integralRoots :
      ∀ n : ℕ, 0 < n →
        ∃ root : (integralClosure baseRing fixedField)ˣ,
          root ^ n = integralValue := by
    intro n hn
    obtain ⟨sourceRoot, sourceRootPower, sourceRootFixed⟩ :=
      fixedRoots n hn
    let fieldRoot : (AlgebraicClosure ℚ_[p])ˣ := fieldEquiv sourceRoot
    have fieldRootPower : fieldRoot ^ n = fieldValue := by
      dsimp [fieldRoot, fieldValue, fieldEquiv]
      rw [← map_pow, sourceRootPower]
    have fieldRootFixed :
        ∀ sigma : LocalAbsoluteGalois p, sigma ∈ subgroup →
          localGaloisUnitsAction p sigma fieldRoot = fieldRoot := by
      intro sigma hsigma
      have fieldRootAction :=
        pair.groupificationEquivAlgebraicClosureUnits_action p sigma sourceRoot
      have augmentation_sigma : pair.augmentation sigma = sigma := rfl
      rw [augmentation_sigma] at fieldRootAction
      rw [← fieldRootAction, sourceRootFixed ⟨sigma, hsigma⟩]
    have fieldRoot_integral :
        IsIntegral baseRing (fieldRoot : AlgebraicClosure ℚ_[p]) := by
      apply IsIntegral.of_pow hn
      rw [← Units.val_pow_eq_pow_val, fieldRootPower]
      exact fieldValue_integral
    have fieldRoot_inverse_integral :
        IsIntegral baseRing (fieldRoot⁻¹ : AlgebraicClosure ℚ_[p]) := by
      apply IsIntegral.of_pow hn
      have inversePower : fieldRoot⁻¹ ^ n = fieldValue⁻¹ := by
        rw [inv_pow, fieldRootPower]
      have underlyingInversePower :
          ((fieldRoot : AlgebraicClosure ℚ_[p])⁻¹) ^ n =
            (fieldValue : AlgebraicClosure ℚ_[p])⁻¹ := by
        simpa only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using
          congrArg Units.val inversePower
      rw [underlyingInversePower]
      exact fieldValue_inverse_integral
    let integralRoot := fixedFieldIntegralUnit p subgroup fieldRoot
      fieldRootFixed fieldRoot_integral fieldRoot_inverse_integral
    refine ⟨integralRoot, ?_⟩
    apply Units.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Units.val fieldRootPower
  letI : FiniteDimensional ℚ_[p] fixedField :=
    fixedField_finiteDimensional p subgroup
  letI : Group.ResiduallyFinite (integralClosure baseRing fixedField)ˣ :=
    integralClosureUnits_residuallyFinite ℚ_[p] fixedField
  have integralValue_eq_one : integralValue = 1 :=
    LocalFieldKummerRigidity.eq_one_of_roots_of_residuallyFinite
      integralValue integralRoots
  have fieldValue_eq_one : fieldValue = 1 := by
    apply Units.ext
    change (fieldValue : AlgebraicClosure ℚ_[p]) = 1
    have underlying := congrArg
      (fun unit : (integralClosure baseRing fixedField)ˣ =>
        (((unit : integralClosure baseRing fixedField) : fixedField) :
          AlgebraicClosure ℚ_[p])) integralValue_eq_one
    rw [integralValue_image] at underlying
    exact underlying.trans (by rfl)
  apply LocalMLFModelTMPair.unitGrothendieckHom_injective p
  apply fieldEquiv.injective
  rw [map_one, map_one]
  exact fieldValue_eq_one

/-- The actual mono-analytic integral-unit Kummer map is injective. -/
theorem monoAnalytic_integralUnitKummerHom_injective :
    Function.Injective
      ((LocalMLFModelTMPair.monoAnalytic p).integralUnitKummerHom p) := by
  intro first second equality
  have quotient_map_eq_one :
      (LocalMLFModelTMPair.monoAnalytic p).integralUnitKummerHom p
          (first / second) = 1 := by
    rw [map_div, equality]
    exact div_self' _
  have quotient_eq_one := monoAnalytic_unit_eq_one_of_Kummer_eq_one p
    (first / second) quotient_map_eq_one
  exact div_eq_one.mp quotient_eq_one

end LocalIntegralUnitKummerInjectivity

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localIntegralUnitKummerInjectivity : Obligation :=
  { id := "IUT-II.local-integral-unit-Kummer-injectivity"
    source := "Absolute Anabelian Topics III, Proposition 3.2(ii), Proposition 3.3(i)"
    status := VerificationStatus.proved
    note :=
      "For the literal mono-analytic Gal(Qbar_p/Q_p) model, equality of the " ++
        "unit-valued Kummer germ with one yields compatible roots of every " ++
        "positive degree fixed by one open subgroup. The associated fixed " ++
        "field is proved finite over Q_p; residual finiteness of its integral-" ++
        "closure unit group forces the original unit to be one. Thus the " ++
        "constructed local integral-unit Kummer homomorphism is injective. " ++
        "This is not the Frobenioid-side comparison of IUT II Definition 4.9."
    dependsOn :=
      [ "IUT-II.local-integral-unit-Kummer-map",
        "IUT-II.local-field-Gm-kummer-rigidity" ] }

end LeanFormal.IUT.Audit
