/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.TateComparisonBoundary
import LeanFormal.IUT.Foundations.Algebra.FiniteCyclicQuotient
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic

/-!
  Source-facing local boundary consumed by later C/D code.

  This record does not claim existence for arbitrary Initial-Theta data.  It
  binds the independent obligations that later algorithms must not mix:
  dependent curve/place/q data, a curve-indexed Tate comparison, split
  multiplicative reduction on the selected local carrier, and an exact finite
  label certificate.  Every projection below is a real consequence of the
  corresponding field.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

structure SourceLocalTateBoundary (l : PrimeGeFive) where
  comparison : InitialThetaTateComparison.{u} l
  splitReduction :
    comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      comparison.finitePlaceInput.place
  localSplitReduction :
    HasSplitMultiplicativeReductionOnMinimalModel
      (NumberFieldFinitePlace.CompletionIntegers
        comparison.finitePlaceInput.place)
      ((comparison.finitePlaceInput.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion
          comparison.finitePlaceInput.place)).curve)
  finiteLabels :
    FiniteCyclicQuotient.IntegerCertificate l.value

namespace SourceLocalTateBoundary

variable {l : PrimeGeFive}

theorem q_order_pos
    (boundary : SourceLocalTateBoundary.{u} l) :
    0 < boundary.comparison.finitePlaceInput.qCandidate.order :=
  boundary.comparison.q_order_pos

theorem q_ne_one
    (boundary : SourceLocalTateBoundary.{u} l) :
    boundary.comparison.finitePlaceInput.qCandidate.q ≠ 1 :=
  boundary.comparison.q_ne_one

theorem stable_reduction
    (boundary : SourceLocalTateBoundary.{u} l) :
    boundary.comparison.finitePlaceInput.arithmetic.curve.HasStableReductionAt
      boundary.comparison.finitePlaceInput.place :=
  boundary.comparison.stable_reduction

theorem split_reduction
    (boundary : SourceLocalTateBoundary.{u} l) :
    boundary.comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      boundary.comparison.finitePlaceInput.place :=
  boundary.splitReduction

theorem local_split_reduction
    (boundary : SourceLocalTateBoundary.{u} l) :
    HasSplitMultiplicativeReductionOnMinimalModel
      (NumberFieldFinitePlace.CompletionIntegers
        boundary.comparison.finitePlaceInput.place)
      ((boundary.comparison.finitePlaceInput.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion
          boundary.comparison.finitePlaceInput.place)).curve) :=
  boundary.localSplitReduction

theorem local_multiplicative_reduction
    (boundary : SourceLocalTateBoundary.{u} l) :
    HasMultiplicativeReductionOnMinimalModel
      (NumberFieldFinitePlace.CompletionIntegers
        boundary.comparison.finitePlaceInput.place)
      ((boundary.comparison.finitePlaceInput.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion
          boundary.comparison.finitePlaceInput.place)).curve) := by
  rcases boundary.localSplitReduction with ⟨C, hC⟩
  exact ⟨C, hC.toHasMultiplicativeReduction⟩

theorem local_stable_reduction
    (boundary : SourceLocalTateBoundary.{u} l) :
    TateCurve.HasStableReductionOnMinimalModel
      (NumberFieldFinitePlace.CompletionIntegers
        boundary.comparison.finitePlaceInput.place)
      ((boundary.comparison.finitePlaceInput.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion
          boundary.comparison.finitePlaceInput.place)).curve) :=
  Or.inr boundary.local_multiplicative_reduction

theorem coordinate_realization
    (boundary : SourceLocalTateBoundary.{u} l) :
    boundary.comparison.curveComparison.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion
            boundary.comparison.finitePlaceInput.place)
          boundary.comparison.finitePlaceInput.qCandidate.q =
      (boundary.comparison.finitePlaceInput.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion
          boundary.comparison.finitePlaceInput.place)).curve :=
  boundary.comparison.coordinate_realization

theorem canonical_curve_elliptic
    (boundary : SourceLocalTateBoundary.{u} l) :
    (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion
        boundary.comparison.finitePlaceInput.place)
      boundary.comparison.finitePlaceInput.qCandidate.q).IsElliptic :=
  boundary.comparison.canonical_curve_elliptic

theorem point_comparison_injective
    (boundary : SourceLocalTateBoundary.{u} l) :
    Function.Injective
      boundary.comparison.local_point_comparison.pointEquiv :=
  boundary.comparison.point_comparison_injective

theorem point_comparison_surjective
    (boundary : SourceLocalTateBoundary.{u} l) :
    Function.Surjective
      boundary.comparison.local_point_comparison.pointEquiv :=
  boundary.comparison.point_comparison_surjective

noncomputable def toTateInput
    (boundary : SourceLocalTateBoundary.{u} l) :
    InitialThetaTateInput.{u} l :=
  boundary.comparison.toTateInput

theorem toTateInput_coordinate
    (boundary : SourceLocalTateBoundary.{u} l) :
    boundary.toTateInput.coordinate_realization =
      boundary.comparison.coordinate_realization := by
  rfl

theorem toTateInput_stable
    (boundary : SourceLocalTateBoundary.{u} l) :
    boundary.toTateInput.arithmetic.curve.HasStableReductionAt
      boundary.toTateInput.place :=
  boundary.toTateInput.stableReduction

noncomputable def toSplitInput
    (boundary : SourceLocalTateBoundary.{u} l) :
    InitialThetaSplitReductionInput.{u} l :=
  boundary.comparison.toSplitInput boundary.splitReduction

theorem toSplitInput_split
    (boundary : SourceLocalTateBoundary.{u} l) :
    (boundary.toSplitInput).splitReduction = boundary.splitReduction := rfl

theorem toSplitInput_stable
    (boundary : SourceLocalTateBoundary.{u} l) :
    (boundary.toSplitInput).arithmetic.curve.HasStableReductionAt
      boundary.toSplitInput.place :=
  InitialThetaSplitReductionInput.stableReduction boundary.toSplitInput

noncomputable def finiteLevelEquiv :
    (boundary : SourceLocalTateBoundary.{u} l) →
    (ℤ ⧸ boundary.finiteLabels.reduction.ker) ≃+ ZMod l.value :=
  fun boundary => boundary.finiteLabels.quotientEquiv

theorem finiteLevelEquiv_apply_mk
    (boundary : SourceLocalTateBoundary.{u} l) (n : ℤ) :
    boundary.finiteLevelEquiv (QuotientAddGroup.mk n) =
      boundary.finiteLabels.reduction n :=
  boundary.finiteLabels.quotientEquiv_apply_mk n

theorem finiteLevel_zero_iff_multiple
    (boundary : SourceLocalTateBoundary.{u} l) (n : ℤ) :
    (QuotientAddGroup.mk n :
      ℤ ⧸ boundary.finiteLabels.reduction.ker) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) :=
  boundary.finiteLabels.quotient_mk_zero_iff_multiple n

theorem finiteLevel_add_multiple
    (boundary : SourceLocalTateBoundary.{u} l) (n k : ℤ) :
    (QuotientAddGroup.mk (n + (l.value : ℤ) * k) :
      ℤ ⧸ boundary.finiteLabels.reduction.ker) =
      QuotientAddGroup.mk n :=
  boundary.finiteLabels.quotient_mk_add_multiple n k

theorem finiteLevel_sub_multiple
    (boundary : SourceLocalTateBoundary.{u} l) (n k : ℤ) :
    (QuotientAddGroup.mk (n - (l.value : ℤ) * k) :
      ℤ ⧸ boundary.finiteLabels.reduction.ker) =
      QuotientAddGroup.mk n :=
  boundary.finiteLabels.quotient_mk_sub_multiple n k

theorem finiteReduction_add_multiple
    (boundary : SourceLocalTateBoundary.{u} l) (n k : ℤ) :
    boundary.finiteLabels.reduction (n + (l.value : ℤ) * k) =
      boundary.finiteLabels.reduction n :=
  boundary.finiteLabels.reduction_add_multiple n k

theorem finiteReduction_sub_multiple
    (boundary : SourceLocalTateBoundary.{u} l) (n k : ℤ) :
    boundary.finiteLabels.reduction (n - (l.value : ℤ) * k) =
      boundary.finiteLabels.reduction n :=
  boundary.finiteLabels.reduction_sub_multiple n k

end SourceLocalTateBoundary

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceLocalTateBoundary : Obligation :=
  { id := "IUT-I.source-local-tate-boundary"
    source := "IUT I, Definition 3.1(b)-(c); source-facing local C boundary"
    status := VerificationStatus.interface
    note :=
      "One dependent record binds the curve-indexed comparison, split local " ++
        "reduction, and exact finite label certificate. Its algebraic and " ++
        "reduction projections are proved, while the existence of the record " ++
        "is intentionally left as the source-faithful C-layer obligation."
    dependsOn :=
      [ "IUT-I.initial-theta-tate-comparison-boundary",
        "Foundations.Geometry.tate-curve-arithmetic-closure",
        "Foundations.Algebra.finite-cyclic-quotient" ] }

end LeanFormal.IUT.Audit
