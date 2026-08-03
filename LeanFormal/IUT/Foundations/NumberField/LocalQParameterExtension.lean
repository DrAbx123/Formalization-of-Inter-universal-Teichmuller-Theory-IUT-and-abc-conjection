import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
  Valuation-theoretic q-candidates along extensions of finite places.

  The actual completion map sends a candidate at the contracted place to a
  candidate upstairs.  The discrete valuation exponent, hence its positive
  natural order, scales by the ramification index.  These results do not
  identify either candidate with the Tate parameter of an elliptic curve.
-/

namespace LeanFormal.IUT

universe u v

noncomputable section

namespace NumberFieldFinitePlace.FinitePlaceQCandidate

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- A valuation-theoretic q-candidate maps to every finite place above it. -/
noncomputable def map
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) :
    FinitePlaceQCandidate place where
  q := completionMap (k := k) place parameter.q
  q_ne_zero := by
    intro h
    exact parameter.q_ne_zero
      (completionMap_injective (k := k) place (by simpa using h))
  valuation_lt_one := by
    rw [← valuation_completionMap (k := k)]
    exact pow_lt_one₀ bot_le parameter.valuation_lt_one
      (ramificationIdx_ne_zero (k := k) place)

@[simp] theorem map_q
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) :
    (map place parameter).q = completionMap (k := k) place parameter.q :=
  rfl

/-- The mapped valuation is the lower valuation raised to the ramification
index. -/
theorem valuation_map
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) :
    (Valued.v (map place parameter).q :
        WithZero (Multiplicative Int)) =
      (Valued.v parameter.q : WithZero (Multiplicative Int)) ^
        (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
          place.maximalIdeal.asIdeal := by
  exact (valuation_completionMap (k := k) place parameter.q).symm

end NumberFieldFinitePlace.FinitePlaceQCandidate

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localQParameterExtensionKernel : Obligation :=
  { id := "Foundations.NumberField.local-q-parameter-extension"
    source :=
      "Ramification of completed finite-place valuations; IUT I, Definition 3.1(c) prerequisite"
    status := VerificationStatus.proved
    note :=
      "Along a finite-place extension, valuation-theoretic q-candidates map " ++
        "through the actual completion embedding, and their multiplicative " ++
        "valuation is the lower valuation raised to the ramification index. " ++
        "No Tate uniformization is inferred."
    dependsOn :=
      [ "Foundations.NumberField.local-q-parameter-valuation",
        "Foundations.NumberField.finite-place-extension" ] }

end LeanFormal.IUT.Audit
