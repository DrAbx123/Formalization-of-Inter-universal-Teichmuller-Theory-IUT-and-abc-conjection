import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.NumberField.LocalQParameterExtension
import Mathlib.Algebra.Group.Int.TypeTags

/-!
  Discrete orders of q-candidates under finite-place extension.

  This file converts the valuation equality in
  `LocalQParameterExtension` first to an equality of integer exponents and
  then to an equality of positive natural orders.
-/

namespace LeanFormal.IUT

universe u v

noncomputable section

namespace NumberFieldFinitePlace.FinitePlaceQCandidate

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The positive integer exponent scales by the ramification index. -/
theorem exponent_map
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) :
    (map place parameter).exponent =
      ((comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
          place.maximalIdeal.asIdeal : Int) * parameter.exponent := by
  let e :=
    (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
      place.maximalIdeal.asIdeal
  have hunzero :
      WithZero.unzero (map place parameter).valuation_ne_zero =
        WithZero.unzero parameter.valuation_ne_zero ^ e := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_pow]
    exact valuation_map (k := k) place parameter
  rw [exponent, exponent, hunzero, Int.toAdd_pow]
  ring

/-- The natural-valued local order scales by the ramification index. -/
theorem order_map
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) :
    (map place parameter).order =
      (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
          place.maximalIdeal.asIdeal * parameter.order := by
  apply Int.ofNat_injective
  change
    ((Int.toNat (map place parameter).exponent : Nat) : Int) =
      (((comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
          place.maximalIdeal.asIdeal * Int.toNat parameter.exponent : Nat) : Int)
  rw [Nat.cast_mul,
    Int.toNat_of_nonneg (le_of_lt (map place parameter).exponent_pos),
    Int.toNat_of_nonneg (le_of_lt parameter.exponent_pos),
    exponent_map (k := k)]

end NumberFieldFinitePlace.FinitePlaceQCandidate

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localQParameterRamificationKernel : Obligation :=
  { id := "Foundations.NumberField.local-q-parameter-ramification"
    source :=
      "Ramification of completed finite-place valuations; IUT I, Definition 3.1(c) prerequisite"
    status := VerificationStatus.proved
    note :=
      "The integer exponent and positive natural order of a mapped " ++
        "valuation-theoretic q-candidate scale by the finite-place " ++
        "ramification index. No local height or Tate-curve statement is " ++
        "inferred."
    dependsOn := ["Foundations.NumberField.local-q-parameter-extension"] }

end LeanFormal.IUT.Audit
