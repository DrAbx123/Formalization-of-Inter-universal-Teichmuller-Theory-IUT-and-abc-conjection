import LeanFormal.IUT.IUTI.InitialTheta.FinitePlaceInput
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import LeanFormal.IUT.Foundations.Geometry.TateDeckAction

namespace LeanFormal.IUT

universe u

noncomputable section

structure InitialThetaTateInput (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l
  place : NumberField.FinitePlace arithmetic.F
  qCandidate : NumberFieldFinitePlace.FinitePlaceQCandidate place
  stableReduction : arithmetic.curve.HasStableReductionAt place
  uniformization :
    CurveIndexedTateUniformization arithmetic.curve place qCandidate

namespace InitialThetaTateInput

variable {l : PrimeGeFive} (input : InitialThetaTateInput.{u} l)

theorem q_order_pos : 0 < input.qCandidate.order :=
  input.qCandidate.order_pos

theorem q_ne_one : input.qCandidate.q ≠ 1 :=
  input.qCandidate.q_ne_one

theorem coordinate_realization :
    input.uniformization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion input.place)
          input.qCandidate.q =
      (input.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion input.place)).curve :=
  input.uniformization.coordinate_realization

theorem deck_subgroup_galois_stable
    (sigma : AlgebraicClosure
        (NumberFieldFinitePlace.Completion input.place)
          ≃ₐ[NumberFieldFinitePlace.Completion input.place]
        AlgebraicClosure (NumberFieldFinitePlace.Completion input.place)) :
    Subgroup.map (Units.map sigma.toRingEquiv.toMonoidHom)
        (Subgroup.zpowers
          (NumberFieldFinitePlace.tateParameterUnit input.place
            input.qCandidate.q input.qCandidate.q_ne_zero)) =
      Subgroup.zpowers
        (NumberFieldFinitePlace.tateParameterUnit input.place
          input.qCandidate.q input.qCandidate.q_ne_zero) := by
  exact NumberFieldFinitePlace.tateParameterDeckSubgroup_algEquiv_map
    input.place input.qCandidate.q input.qCandidate.q_ne_zero sigma

end InitialThetaTateInput

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaTateInput : Obligation :=
  { id := "IUT-I.initial-theta-tate-input"
    source := "IUT I, Definition 3.1(b),(c); local Tate input"
    status := VerificationStatus.interface
    note :=
      "A dependent record forces one arithmetic curve, one actual finite " ++
        "place, one valuation-theoretic q candidate, stable reduction, and " ++
        "the complete curve-indexed Tate-uniformization contract to coexist. " ++
        "The q-order, q-ne-one, coordinate realization, and deck-subgroup " ++
        "Galois stability are proved projections. No constructor is supplied " ++
        "because the source stable-reduction and Tate-uniformization theorems " ++
        "remain genuine C-layer obligations."
    dependsOn :=
      [ "IUT-I.initial-theta-finite-place-input",
        "Foundations.Geometry.curve-indexed-tate-uniformization",
        "Foundations.Geometry.tate-deck-galois-action" ] }

end LeanFormal.IUT.Audit
