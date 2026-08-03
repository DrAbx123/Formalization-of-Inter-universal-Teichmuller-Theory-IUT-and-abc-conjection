import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

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

universe u

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
        "positive powers are proved. This is not yet a Tate parameter of a " ++
        "specified elliptic curve."
    dependsOn := ["Foundations.NumberField.finite-places"] }

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
