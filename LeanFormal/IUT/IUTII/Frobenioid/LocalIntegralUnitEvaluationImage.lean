import LeanFormal.IUT.IUTII.Frobenioid.LocalMLFPrimeStripBridge

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

/-!
  The exact image of the local integral-unit evaluation.

  IUT II, Definition 4.9(i), evaluates the Frobenioid monoid at a universal
  covering pro-object and then takes its unit group.  This file proves the
  corresponding arithmetic carrier statement for the concrete local model:
  the units of the nonzero integral-closure monoid are exactly the
  algebraic-closure units whose value and inverse are integral.  The resulting
  equivalence is Galois-equivariant and descends to a compatible `times-mu`
  Kummer isomorphism preserving every open-subgroup invariant image.

  This is not yet the categorical construction of the universal-cover
  pro-object or of the Frobenioid evaluation functor.
-/

namespace LeanFormal.IUT

namespace LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

def evaluatedUnitSubgroup :
    Subgroup (AlgebraicClosure ℚ_[p])ˣ where
  carrier := { unit |
    IsIntegral
        (Valuation.integer (ValuativeRel.valuation ℚ_[p]))
        (unit.val : AlgebraicClosure ℚ_[p]) ∧
      IsIntegral
        (Valuation.integer (ValuativeRel.valuation ℚ_[p]))
        (unit.val : AlgebraicClosure ℚ_[p])⁻¹ }
  one_mem' := ⟨isIntegral_one, by simpa using isIntegral_one⟩
  mul_mem' := by
    intro first second hfirst hsecond
    constructor
    · exact hfirst.1.mul hsecond.1
    · change IsIntegral
        (Valuation.integer (ValuativeRel.valuation ℚ_[p]))
        (((first.val : AlgebraicClosure ℚ_[p]) *
          (second.val : AlgebraicClosure ℚ_[p]))⁻¹)
      simpa only [mul_inv_rev] using hsecond.2.mul hfirst.2
  inv_mem' := by
    intro unit hunit
    constructor
    · simpa only [Units.val_inv_eq_inv_val] using hunit.2
    · simpa only [Units.val_inv_eq_inv_val, inv_inv] using hunit.1

theorem unitEvaluation_mem_evaluatedUnitSubgroup
    (unit : (LocalIntegralMonoid p)ˣ) :
    unitEvaluation p unit ∈ evaluatedUnitSubgroup p := by
  constructor
  · exact unit.val.1.property
  · have inverse_eq :
        (unit.inv.1.1 : AlgebraicClosure ℚ_[p]) =
          ((unitEvaluation p unit).val : AlgebraicClosure ℚ_[p])⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      exact congrArg
        (fun value : LocalIntegralMonoid p ↦
          (value.1.1 : AlgebraicClosure ℚ_[p]))
        unit.inv_val
    rw [← inverse_eq]
    exact unit.inv.1.property

noncomputable def unitEvaluationToImage :
    (LocalIntegralMonoid p)ˣ →* evaluatedUnitSubgroup p where
  toFun unit :=
    ⟨unitEvaluation p unit,
      unitEvaluation_mem_evaluatedUnitSubgroup p unit⟩
  map_one' := Subtype.ext (map_one (unitEvaluation p))
  map_mul' first second :=
    Subtype.ext (map_mul (unitEvaluation p) first second)

theorem unitEvaluationToImage_injective :
    Function.Injective (unitEvaluationToImage p) := by
  intro first second equality
  apply unitEvaluation_injective p
  exact congrArg Subtype.val equality

theorem unitEvaluationToImage_surjective :
    Function.Surjective (unitEvaluationToImage p) := by
  intro target
  let integralValue : LocalAlgebraicIntegerRing p :=
    ⟨(target : (AlgebraicClosure ℚ_[p])ˣ), target.property.1⟩
  let integralInverse : LocalAlgebraicIntegerRing p :=
    ⟨Inv.inv ((target : (AlgebraicClosure ℚ_[p])ˣ).val),
      target.property.2⟩
  have integralValue_ne_zero : integralValue ≠ 0 := by
    intro equality
    apply (target : (AlgebraicClosure ℚ_[p])ˣ).ne_zero
    exact congrArg Subtype.val equality
  have integralInverse_ne_zero : integralInverse ≠ 0 := by
    intro equality
    have underlying :
        ((target : (AlgebraicClosure ℚ_[p])ˣ).val :
          AlgebraicClosure ℚ_[p])⁻¹ = 0 := by
      simpa [integralInverse] using congrArg Subtype.val equality
    exact (inv_ne_zero
      (target : (AlgebraicClosure ℚ_[p])ˣ).ne_zero) underlying
  let monoidValue : LocalIntegralMonoid p :=
    ⟨integralValue,
      mem_nonZeroDivisors_of_ne_zero integralValue_ne_zero⟩
  let monoidInverse : LocalIntegralMonoid p :=
    ⟨integralInverse,
      mem_nonZeroDivisors_of_ne_zero integralInverse_ne_zero⟩
  let source : (LocalIntegralMonoid p)ˣ :=
    { val := monoidValue
      inv := monoidInverse
      val_inv := by
        apply Subtype.ext
        apply Subtype.ext
        change
          ((target : (AlgebraicClosure ℚ_[p])ˣ).val :
              AlgebraicClosure ℚ_[p]) *
            ((target : (AlgebraicClosure ℚ_[p])ˣ).val :
              AlgebraicClosure ℚ_[p])⁻¹ = 1
        exact mul_inv_cancel₀
          (target : (AlgebraicClosure ℚ_[p])ˣ).ne_zero
      inv_val := by
        apply Subtype.ext
        apply Subtype.ext
        change
          ((target : (AlgebraicClosure ℚ_[p])ˣ).val :
              AlgebraicClosure ℚ_[p])⁻¹ *
            ((target : (AlgebraicClosure ℚ_[p])ˣ).val :
              AlgebraicClosure ℚ_[p]) = 1
        exact inv_mul_cancel₀
          (target : (AlgebraicClosure ℚ_[p])ˣ).ne_zero }
  refine ⟨source, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rfl

noncomputable def unitEvaluationEquiv :
    (LocalIntegralMonoid p)ˣ ≃* evaluatedUnitSubgroup p :=
  MulEquiv.ofBijective
    (unitEvaluationToImage p)
    ⟨unitEvaluationToImage_injective p,
      unitEvaluationToImage_surjective p⟩

@[simp]
theorem unitEvaluationEquiv_coe
    (unit : (LocalIntegralMonoid p)ˣ) :
    ((unitEvaluationEquiv p unit : evaluatedUnitSubgroup p) :
        (AlgebraicClosure ℚ_[p])ˣ) =
      unitEvaluation p unit :=
  rfl

noncomputable def evaluatedUnitAction :
    LocalAbsoluteGalois p →* MulAut (evaluatedUnitSubgroup p) :=
  (MulAut.congr (unitEvaluationEquiv p)).toMonoidHom.comp
    (unitAction p)

theorem unitEvaluationEquiv_equivariant
    (g : LocalAbsoluteGalois p)
    (unit : (LocalIntegralMonoid p)ˣ) :
    unitEvaluationEquiv p (unitAction p g unit) =
      evaluatedUnitAction p g (unitEvaluationEquiv p unit) := by
  simp [evaluatedUnitAction, MulAut.congr]

theorem evaluatedUnitAction_coe
    (g : LocalAbsoluteGalois p)
    (unit : evaluatedUnitSubgroup p) :
    ((evaluatedUnitAction p g unit : evaluatedUnitSubgroup p) :
        (AlgebraicClosure ℚ_[p])ˣ) =
      localGaloisUnitsAction p g
        ((unit : evaluatedUnitSubgroup p) :
          (AlgebraicClosure ℚ_[p])ˣ) := by
  obtain ⟨source, rfl⟩ := (unitEvaluationEquiv p).surjective unit
  rw [← unitEvaluationEquiv_equivariant]
  change unitEvaluation p (unitAction p g source) =
    localGaloisUnitsAction p g (unitEvaluation p source)
  exact unitEvaluation_equivariant p g source

noncomputable def timesMuUnitEvaluationEquiv :
    TimesMuQuotient (LocalIntegralMonoid p)ˣ ≃*
      TimesMuQuotient (evaluatedUnitSubgroup p) :=
  QuotientGroup.congr
    (CommGroup.torsion (LocalIntegralMonoid p)ˣ)
    (CommGroup.torsion (evaluatedUnitSubgroup p))
    (unitEvaluationEquiv p)
    (unitEvaluationEquiv p).map_torsion

@[simp]
theorem timesMuUnitEvaluationEquiv_quotientMap
    (unit : (LocalIntegralMonoid p)ˣ) :
    timesMuUnitEvaluationEquiv p
        (TimesMuQuotient.quotientMap unit) =
      TimesMuQuotient.quotientMap (unitEvaluationEquiv p unit) :=
  rfl

noncomputable def timesMuEvaluationComparison :
    TimesMuKummer.Isomorphism
      (unitAction p) (evaluatedUnitAction p) where
  equiv := timesMuUnitEvaluationEquiv p
  equivariant := by
    intro g value
    obtain ⟨unit, rfl⟩ :=
      TimesMuQuotient.quotientMap_surjective value
    simp only [TimesMuQuotient.action_quotientMap,
      timesMuUnitEvaluationEquiv_quotientMap,
      unitEvaluationEquiv_equivariant]
  invariantImage := by
    intro subgroup
    ext value
    constructor
    · rintro ⟨sourceValue, sourceMember, rfl⟩
      rcases
          (TimesMuKummer.mem_invariantImage_iff
            (unitAction p) subgroup sourceValue).mp sourceMember with
        ⟨unit, fixed, rfl⟩
      rw [timesMuUnitEvaluationEquiv_quotientMap]
      apply
        (TimesMuKummer.mem_invariantImage_iff
          (evaluatedUnitAction p) subgroup _).mpr
      refine ⟨unitEvaluationEquiv p unit, ?_, rfl⟩
      intro g
      rw [← unitEvaluationEquiv_equivariant]
      exact congrArg (unitEvaluationEquiv p) (fixed g)
    · intro targetMember
      rcases
          (TimesMuKummer.mem_invariantImage_iff
            (evaluatedUnitAction p) subgroup value).mp targetMember with
        ⟨targetUnit, fixed, rfl⟩
      let sourceUnit := (unitEvaluationEquiv p).symm targetUnit
      have sourceFixed :
          ∀ g : subgroup,
            unitAction p (g : LocalAbsoluteGalois p) sourceUnit =
              sourceUnit := by
        intro g
        apply (unitEvaluationEquiv p).injective
        simp only [unitEvaluationEquiv_equivariant, sourceUnit,
          (unitEvaluationEquiv p).apply_symm_apply, fixed g]
      refine
        ⟨TimesMuQuotient.quotientMap sourceUnit,
          (TimesMuKummer.mem_invariantImage_iff
            (unitAction p) subgroup _).mpr
              ⟨sourceUnit, sourceFixed, rfl⟩,
          ?_⟩
      rw [timesMuUnitEvaluationEquiv_quotientMap]
      exact congrArg TimesMuQuotient.quotientMap
        ((unitEvaluationEquiv p).apply_symm_apply targetUnit)

noncomputable def timesMuEvaluationOrbit :
    TimesMuKummer.Isomorphism.Orbit
      (unitAction p) (evaluatedUnitAction p) :=
  TimesMuKummer.Isomorphism.orbitOf
    (timesMuEvaluationComparison p)

end LocalIntegralMonoid

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localIntegralUnitEvaluationImage : Obligation :=
  { id := "IUT-II.local-integral-unit-evaluation-image"
    source := "IUT II, Definition 4.9(i); local unit evaluation and times-mu carrier"
    status := VerificationStatus.proved
    note :=
      "The local integral-unit evaluation is proved to have exactly the " ++
        "algebraic-closure units whose value and inverse are integral. The " ++
        "resulting multiplicative equivalence is Galois-equivariant, descends " ++
        "to the full-torsion quotient, and preserves every open-subgroup " ++
        "invariant image, yielding an actual carrier-level Ism orbit. The " ++
        "universal-cover pro-object, categorical Frobenioid O-triangle " ++
        "evaluation, ind-topology, and group-reconstruction identification " ++
        "remain separate obligations."
    dependsOn :=
      [ "IUT-II.local-integral-monoid-carrier",
        "IUT-II.local-times-mu-evaluation",
        "IUT-II.local-MLF-prime-strip-bridge",
        "IUT-II.times-mu-ism-orbit" ] }

end LeanFormal.IUT.Audit
