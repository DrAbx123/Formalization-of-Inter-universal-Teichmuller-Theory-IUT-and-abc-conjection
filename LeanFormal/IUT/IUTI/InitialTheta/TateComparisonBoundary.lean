/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.TateInput
import LeanFormal.IUT.IUTI.InitialTheta.SplitReductionInput
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary

/-!
  Composition boundary for the Initial-Theta local Tate input.

  The arithmetic curve, finite place, q-candidate, and point comparison are
  dependent data.  Keeping them in one record prevents a coordinate change
  proved for one local curve from being silently reused for another.  The
  record has no constructor from stable reduction alone: a genuine Tate
  comparison must be supplied by the source-faithful C-layer proof.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

structure InitialThetaTateComparison (l : PrimeGeFive) where
  finitePlaceInput : InitialThetaFinitePlaceInput.{u} l
  curveComparison : TateCurveComparison
    finitePlaceInput.arithmetic.curve
    finitePlaceInput.place
    finitePlaceInput.qCandidate

namespace InitialThetaTateComparison

variable {l : PrimeGeFive}

theorem arithmetic_curve
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.finitePlaceInput.arithmetic.curve =
      comparison.finitePlaceInput.arithmetic.curve := rfl

theorem finite_place
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.finitePlaceInput.place = comparison.finitePlaceInput.place := rfl

theorem q_candidate
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.finitePlaceInput.qCandidate =
      comparison.finitePlaceInput.qCandidate := rfl

theorem q_order_pos
    (comparison : InitialThetaTateComparison.{u} l) :
    0 < comparison.finitePlaceInput.qCandidate.order :=
  comparison.finitePlaceInput.q_order_pos

theorem q_ne_one
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.finitePlaceInput.qCandidate.q ≠ 1 :=
  comparison.finitePlaceInput.q_ne_one

theorem stable_reduction
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.finitePlaceInput.arithmetic.curve.HasStableReductionAt
      comparison.finitePlaceInput.place :=
  comparison.finitePlaceInput.stableReduction

theorem coordinate_realization
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.curveComparison.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion
            comparison.finitePlaceInput.place)
          comparison.finitePlaceInput.qCandidate.q =
      (comparison.finitePlaceInput.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion
          comparison.finitePlaceInput.place)).curve :=
  comparison.curveComparison.coordinate_realization

theorem canonical_curve_elliptic
    (comparison : InitialThetaTateComparison.{u} l) :
    (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion comparison.finitePlaceInput.place)
      comparison.finitePlaceInput.qCandidate.q).IsElliptic :=
  comparison.curveComparison.canonical_elliptic

def local_point_comparison
    (comparison : InitialThetaTateComparison.{u} l) :
    TatePointComparison
      comparison.finitePlaceInput.arithmetic.curve
      comparison.finitePlaceInput.place
      comparison.finitePlaceInput.qCandidate :=
  comparison.curveComparison.point_comparison

noncomputable def toTateInput
    (comparison : InitialThetaTateComparison.{u} l) :
    InitialThetaTateInput.{u} l :=
  { arithmetic := comparison.finitePlaceInput.arithmetic
    place := comparison.finitePlaceInput.place
    qCandidate := comparison.finitePlaceInput.qCandidate
    stableReduction := comparison.finitePlaceInput.stableReduction
    uniformization := comparison.curveComparison.toUniformization }

@[simp] theorem toTateInput_arithmetic
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.toTateInput.arithmetic = comparison.finitePlaceInput.arithmetic := rfl

@[simp] theorem toTateInput_place
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.toTateInput.place = comparison.finitePlaceInput.place := rfl

@[simp] theorem toTateInput_qCandidate
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.toTateInput.qCandidate = comparison.finitePlaceInput.qCandidate := rfl

theorem toTateInput_stable
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.toTateInput.arithmetic.curve.HasStableReductionAt
      comparison.toTateInput.place :=
  comparison.toTateInput.stableReduction

theorem toTateInput_q_order_pos
    (comparison : InitialThetaTateComparison.{u} l) :
    0 < comparison.toTateInput.qCandidate.order :=
  comparison.toTateInput.q_order_pos

theorem toTateInput_q_ne_one
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.toTateInput.qCandidate.q ≠ 1 :=
  comparison.toTateInput.q_ne_one

theorem toTateInput_coordinate_realization
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.toTateInput.uniformization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion comparison.toTateInput.place)
          comparison.toTateInput.qCandidate.q =
      (comparison.toTateInput.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion comparison.toTateInput.place)).curve :=
  comparison.toTateInput.coordinate_realization

theorem toTateInput_deck_subgroup_stable
    (comparison : InitialThetaTateComparison.{u} l)
    (sigma : AlgebraicClosure
        (NumberFieldFinitePlace.Completion comparison.toTateInput.place)
          ≃ₐ[NumberFieldFinitePlace.Completion comparison.toTateInput.place]
        AlgebraicClosure
          (NumberFieldFinitePlace.Completion comparison.toTateInput.place)) :
    Subgroup.map (Units.map sigma.toRingEquiv.toMonoidHom)
        (Subgroup.zpowers
          (NumberFieldFinitePlace.tateParameterUnit
            comparison.toTateInput.place comparison.toTateInput.qCandidate.q
            comparison.toTateInput.qCandidate.q_ne_zero)) =
      Subgroup.zpowers
        (NumberFieldFinitePlace.tateParameterUnit
          comparison.toTateInput.place comparison.toTateInput.qCandidate.q
          comparison.toTateInput.qCandidate.q_ne_zero) := by
  exact comparison.toTateInput.deck_subgroup_galois_stable sigma

noncomputable def toSplitInput
    (comparison : InitialThetaTateComparison.{u} l)
    (split : comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      comparison.finitePlaceInput.place) :
    InitialThetaSplitReductionInput.{u} l :=
  { arithmetic := comparison.finitePlaceInput.arithmetic
    place := comparison.finitePlaceInput.place
    qCandidate := comparison.finitePlaceInput.qCandidate
    splitReduction := split }

@[simp] theorem toSplitInput_arithmetic
    (comparison : InitialThetaTateComparison.{u} l)
    (split : comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      comparison.finitePlaceInput.place) :
    (comparison.toSplitInput split).arithmetic =
      comparison.finitePlaceInput.arithmetic := rfl

@[simp] theorem toSplitInput_place
    (comparison : InitialThetaTateComparison.{u} l)
    (split : comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      comparison.finitePlaceInput.place) :
    (comparison.toSplitInput split).place = comparison.finitePlaceInput.place := rfl

@[simp] theorem toSplitInput_qCandidate
    (comparison : InitialThetaTateComparison.{u} l)
    (split : comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      comparison.finitePlaceInput.place) :
    (comparison.toSplitInput split).qCandidate =
      comparison.finitePlaceInput.qCandidate := rfl

theorem toSplitInput_split
    (comparison : InitialThetaTateComparison.{u} l)
    (split : comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      comparison.finitePlaceInput.place) :
    (comparison.toSplitInput split).arithmetic.curve.HasSplitMultiplicativeReductionAt
      (comparison.toSplitInput split).place :=
  split

theorem toSplitInput_stable
    (comparison : InitialThetaTateComparison.{u} l)
    (split : comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      comparison.finitePlaceInput.place) :
    (comparison.toSplitInput split).arithmetic.curve.HasStableReductionAt
      (comparison.toSplitInput split).place := by
  exact InitialThetaSplitReductionInput.stableReduction
    (comparison.toSplitInput split)

theorem point_comparison_galois
    (comparison : InitialThetaTateComparison.{u} l)
    (sigma : AlgebraicClosure
        (NumberFieldFinitePlace.Completion comparison.finitePlaceInput.place)
          ≃ₐ[NumberFieldFinitePlace.Completion comparison.finitePlaceInput.place]
        AlgebraicClosure
          (NumberFieldFinitePlace.Completion comparison.finitePlaceInput.place))
    (x : (AlgebraicClosure
      (NumberFieldFinitePlace.Completion comparison.finitePlaceInput.place))ˣ) :
    (comparison.local_point_comparison).pointEquiv
        (QuotientGroup.mk (Units.map sigma.toRingEquiv.toMonoidHom x)) =
      Multiplicative.ofAdd
        ((comparison.finitePlaceInput.arithmetic.curve.baseChange
          (NumberFieldFinitePlace.Completion comparison.finitePlaceInput.place)).galoisActionOnPoint
            sigma ((comparison.local_point_comparison).pointEquiv
              (QuotientGroup.mk x)).toAdd) := by
  exact comparison.local_point_comparison.galois_naturality sigma x

theorem point_comparison_injective
    (comparison : InitialThetaTateComparison.{u} l) :
    Function.Injective comparison.local_point_comparison.pointEquiv :=
  comparison.local_point_comparison.pointEquiv.injective

theorem point_comparison_surjective
    (comparison : InitialThetaTateComparison.{u} l) :
    Function.Surjective comparison.local_point_comparison.pointEquiv :=
  comparison.local_point_comparison.pointEquiv.surjective

theorem toTateInput_uniformization
    (comparison : InitialThetaTateComparison.{u} l) :
    comparison.toTateInput.uniformization =
      comparison.curveComparison.toUniformization := rfl

end InitialThetaTateComparison

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaTateComparisonBoundary : Obligation :=
  { id := "IUT-I.initial-theta-tate-comparison-boundary"
    source := "IUT I, Definition 3.1(b)-(c); dependent local Tate comparison"
    status := VerificationStatus.interface
    note :=
      "The dependent arithmetic/place/q carrier and the separate coordinate " ++
        "and point comparison are composed without changing their mathematical " ++
        "types. Stable reduction and split-reduction projections are proved; " ++
        "the comparison itself remains an explicit source-faithful obligation."
    dependsOn :=
      [ "IUT-I.initial-theta-tate-input",
        "Foundations.Geometry.tate-point-quotient-boundary" ] }

end LeanFormal.IUT.Audit
