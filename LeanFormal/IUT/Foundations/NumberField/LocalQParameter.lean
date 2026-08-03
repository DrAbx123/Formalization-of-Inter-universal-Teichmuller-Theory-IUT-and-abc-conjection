import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

/-!
  The valuation-theoretic kernel of a local q-parameter.

  A genuine Tate parameter for an elliptic curve must also come with a Tate
  uniformization theorem identifying the curve with the corresponding
  multiplicative quotient.  Mathlib 4.32.2 does not currently provide that
  theorem.  The structure below is therefore deliberately called a
  `FinitePlaceQCandidate`: it records only the nonzero element and strict
  valuation inequality that can be constructed from the completed DVR.

  Source comparison: IUT I, Definition 3.1(c), and the discussion of the
  q-parameter in Section 3; compare `promachina/iut-lean`,
  `Iut/Foundations/SourceInitialThetaData.lean`, `ThetaTateParameterData`.
-/

namespace LeanFormal.IUT

universe u v

noncomputable section

namespace NumberFieldFinitePlace

variable {K : Type u} [Field K] [NumberField K]

abbrev Completion (place : NumberField.FinitePlace K) :=
  (underlyingPrime place).adicCompletion K

abbrev CompletionIntegers (place : NumberField.FinitePlace K) :=
  (underlyingPrime place).adicCompletionIntegers K

/--
The valuation-theoretic data satisfied by a Tate q-parameter, without the
unproved assertion that it uniformizes a specified elliptic curve.
-/
structure FinitePlaceQCandidate (place : NumberField.FinitePlace K) where
  q : Completion place
  q_ne_zero : q ≠ 0
  valuation_lt_one :
    (Valued.v q : WithZero (Multiplicative Int)) < 1

namespace FinitePlaceQCandidate

variable {place : NumberField.FinitePlace K}

theorem valuation_ne_zero (parameter : FinitePlaceQCandidate place) :
    (Valued.v parameter.q : WithZero (Multiplicative Int)) ≠ 0 := by
  intro h
  exact parameter.q_ne_zero
    (((Valued.v :
      Valuation (Completion place) (WithZero (Multiplicative Int))).map_eq_zero_iff).mp h)

theorem q_ne_one (parameter : FinitePlaceQCandidate place) :
    parameter.q ≠ 1 := by
  intro h
  have hlt := parameter.valuation_lt_one
  rw [h] at hlt
  have hone :
      (1 : WithZero (Multiplicative Int)) < 1 := by
    simpa only [map_one] using hlt
  exact (lt_irrefl 1) hone

/-- Minus the additive exponent of the multiplicative discrete valuation. -/
noncomputable def exponent (parameter : FinitePlaceQCandidate place) : Int :=
  -Multiplicative.toAdd
    (WithZero.unzero parameter.valuation_ne_zero)

theorem exponent_pos (parameter : FinitePlaceQCandidate place) :
    0 < parameter.exponent := by
  have valuationExponent_neg :
      Multiplicative.toAdd
          (WithZero.unzero parameter.valuation_ne_zero) < 0 := by
    exact WithZero.toAdd_unzero_lt_of_lt_ofAdd
      parameter.valuation_ne_zero parameter.valuation_lt_one
  simpa [exponent] using neg_pos.mpr valuationExponent_neg

/-- The positive natural-valued local order attached to the candidate. -/
noncomputable def order (parameter : FinitePlaceQCandidate place) : Nat :=
  Int.toNat parameter.exponent

theorem order_pos (parameter : FinitePlaceQCandidate place) :
    0 < parameter.order := by
  rw [order]
  apply Nat.pos_of_ne_zero
  intro h
  exact (not_le_of_gt parameter.exponent_pos) (Int.toNat_eq_zero.mp h)

/-- Positive powers preserve the strict q-parameter valuation condition. -/
noncomputable def pow (parameter : FinitePlaceQCandidate place)
    (n : Nat) (hn : 0 < n) : FinitePlaceQCandidate place where
  q := parameter.q ^ n
  q_ne_zero := pow_ne_zero n parameter.q_ne_zero
  valuation_lt_one := by
    rw [map_pow]
    exact pow_lt_one₀ bot_le parameter.valuation_lt_one hn.ne'

@[simp] theorem pow_q (parameter : FinitePlaceQCandidate place)
    (n : Nat) (hn : 0 < n) :
    (parameter.pow n hn).q = parameter.q ^ n :=
  rfl

section Extension

variable {k : Type v} [Field k] [NumberField k] [Algebra k K]

/-- A valuation-theoretic q-candidate maps to every finite place above it. -/
noncomputable def map
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) :
    FinitePlaceQCandidate place where
  q := completionMap (k := k) place parameter.q
  q_ne_zero := by
    intro h
    exact parameter.q_ne_zero
      (completionMap_injective place (by simpa using h))
  valuation_lt_one := by
    rw [← valuation_completionMap]
    exact pow_lt_one₀ bot_le parameter.valuation_lt_one
      (ramificationIdx_ne_zero place)

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
  exact (valuation_completionMap place parameter.q).symm

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
    exact valuation_map place parameter
  rw [exponent, exponent, hunzero, Int.toAdd_pow]
  push_cast
  ring

/-- The natural-valued local order scales by the ramification index. -/
theorem order_map
    (place : NumberField.FinitePlace K)
    (parameter : FinitePlaceQCandidate (comap (k := k) place)) :
    (map place parameter).order =
      (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
          place.maximalIdeal.asIdeal * parameter.order := by
  apply Int.ofNat_injective
  rw [Int.ofNat_toNat (le_of_lt (map place parameter).exponent_pos),
    Nat.cast_mul, Int.ofNat_toNat (le_of_lt parameter.exponent_pos),
    exponent_map]

end Extension

end FinitePlaceQCandidate

/--
Every completed finite place contains valuation-theoretic q-candidates.  This
is a DVR fact and does not select the Tate parameter of any elliptic curve.
-/
theorem finitePlaceQCandidate_nonempty
    (place : NumberField.FinitePlace K) :
    Nonempty (FinitePlaceQCandidate place) := by
  let prime := underlyingPrime place
  obtain ⟨uniformizer, hUniformizer⟩ :=
    IsDiscreteValuationRing.exists_irreducible
      (prime.adicCompletionIntegers K)
  refine ⟨{
    q := (uniformizer : prime.adicCompletion K)
    q_ne_zero := ?_
    valuation_lt_one := ?_ }⟩
  · exact Subtype.coe_ne_coe.mpr hUniformizer.ne_zero
  · exact Valuation.integer.v_irreducible_lt_one hUniformizer

end NumberFieldFinitePlace

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localQParameterValuationKernel : Obligation :=
  { id := "Foundations.NumberField.local-q-parameter-valuation"
    source := "Completed DVR valuation theory; IUT I, Definition 3.1(c) prerequisite"
    status := VerificationStatus.proved
    note :=
      "At every actual number-field finite completion, an irreducible " ++
        "element of the completed DVR gives a nonzero q-candidate of " ++
        "valuation below one. Its positive discrete order and closure under " ++
        "positive powers are proved. Along a finite-place extension, candidates " ++
        "map through the actual completion embedding, and their valuation " ++
        "exponent and natural order scale by the ramification index. This is " ++
        "not yet a Tate parameter of a specified elliptic curve."
    dependsOn :=
      [ "Foundations.NumberField.finite-places",
        "Foundations.NumberField.finite-place-extension" ] }

def ellipticTateUniformization : Obligation :=
  { id := "Foundations.Geometry.elliptic-tate-uniformization"
    source := "Tate uniformization at split multiplicative places; IUT I, Definition 3.1(c)"
    status := VerificationStatus.pending
    note :=
      "No theorem currently identifies a split-multiplicative elliptic curve " ++
        "over the finite completion with the quotient by powers of a " ++
        "q-parameter, proves Galois equivariance, or relates the parameter " ++
        "order to the curve's local height. A structure field containing such " ++
        "an equivalence is not counted as a proof."
    dependsOn :=
      [ "Foundations.NumberField.local-q-parameter-valuation",
        "Foundations.Geometry.elliptic-local-reduction" ] }

end LeanFormal.IUT.Audit
