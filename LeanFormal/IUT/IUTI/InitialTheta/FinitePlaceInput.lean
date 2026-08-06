import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
  A typed finite-place input boundary for Initial Theta data.

  The carrier uses the same arithmetic curve and an actual Mathlib finite
  place.  The q-candidate is constructed from the completed DVR; stable
  reduction is an explicit hypothesis, so this record cannot be mistaken for
  a theorem selecting a bad place or proving Tate uniformization.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

structure InitialThetaFinitePlaceInput (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l
  place : NumberField.FinitePlace arithmetic.F
  qCandidate :
    NumberFieldFinitePlace.FinitePlaceQCandidate place
  stableReduction : arithmetic.curve.HasStableReductionAt place

noncomputable def InitialThetaFinitePlaceInput.ofStable
    (l : PrimeGeFive) (arithmetic : InitialThetaArithmeticData.{u} l)
    (place : NumberField.FinitePlace arithmetic.F)
    (stableReduction : arithmetic.curve.HasStableReductionAt place) :
    InitialThetaFinitePlaceInput l where
  arithmetic := arithmetic
  place := place
  qCandidate :=
    Classical.choice
      (NumberFieldFinitePlace.finitePlaceQCandidate_nonempty place)
  stableReduction := stableReduction

theorem InitialThetaFinitePlaceInput.q_order_pos
    {l : PrimeGeFive} (input : InitialThetaFinitePlaceInput.{u} l) :
    0 < input.qCandidate.order :=
  input.qCandidate.order_pos

theorem InitialThetaFinitePlaceInput.q_ne_one
    {l : PrimeGeFive} (input : InitialThetaFinitePlaceInput.{u} l) :
    input.qCandidate.q ≠ 1 :=
  input.qCandidate.q_ne_one

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaFinitePlaceInput : Obligation :=
  { id := "IUT-I.initial-theta-finite-place-input"
    source := "IUT I, Definition 3.1(b),(c)"
    status := VerificationStatus.interface
    note :=
      "The same arithmetic curve, actual finite place, DVR q-candidate, and " ++
        "stable-reduction premise are packaged in one typed input. The q " ++
        "candidate is constructed, while place selection, split multiplicative " ++
        "reduction, and Tate uniformization remain explicit obligations."
    dependsOn :=
      [ "IUT-I.initial-theta-arithmetic-data",
        "Foundations.NumberField.local-q-parameter-valuation",
        "IUT-I.initial-theta-reduction-place-partition" ] }

end LeanFormal.IUT.Audit
