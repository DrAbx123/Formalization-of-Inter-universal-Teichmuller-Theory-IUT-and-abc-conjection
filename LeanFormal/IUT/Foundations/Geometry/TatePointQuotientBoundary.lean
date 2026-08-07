/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateDeckQuotient
import LeanFormal.IUT.Foundations.Geometry.TateDeckAction
import LeanFormal.IUT.Foundations.Algebra.CyclicQuotient
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
  A source-faithful boundary for the point part of Tate uniformization.

  The algebraic quotient and its Galois transport are proved in the imported
  modules.  This file records only the genuinely missing comparison with the
  algebraic-closure points of the selected curve, then combines it with the
  coordinate comparison.  The comparison is intentionally a field of a
  structure: no analytic existence theorem is smuggled in by a definition.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

structure TatePointComparison
    {F : Type u} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) where
  pointEquiv :
    ((AlgebraicClosure (NumberFieldFinitePlace.Completion place))ˣ ⧸
      Subgroup.zpowers
        (NumberFieldFinitePlace.tateParameterUnit
          place parameter.q parameter.q_ne_zero)) ≃*
      Multiplicative
        (X.baseChange (NumberFieldFinitePlace.Completion place)).AlgebraicClosurePoint
  galois_naturality :
    ∀ (sigma :
        AlgebraicClosure (NumberFieldFinitePlace.Completion place) ≃ₐ[
          NumberFieldFinitePlace.Completion place]
        AlgebraicClosure (NumberFieldFinitePlace.Completion place))
      (x : (AlgebraicClosure
        (NumberFieldFinitePlace.Completion place))ˣ),
      pointEquiv (QuotientGroup.mk
        (Units.map sigma.toRingEquiv.toMonoidHom x)) =
        Multiplicative.ofAdd
          ((X.baseChange (NumberFieldFinitePlace.Completion place)).galoisActionOnPoint
            sigma (pointEquiv (QuotientGroup.mk x)).toAdd)

namespace TatePointComparison

variable {F : Type u} [Field F] [NumberField F]
variable {X : PuncturedEllipticCurve F}
variable {place : NumberField.FinitePlace F}
variable {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}

abbrev LocalUnit := (AlgebraicClosure
  (NumberFieldFinitePlace.Completion place))ˣ

abbrev DeckQuotient := LocalUnit ⧸ Subgroup.zpowers
  (NumberFieldFinitePlace.tateParameterUnit
    place parameter.q parameter.q_ne_zero)

theorem pointEquiv_injective
    (comparison : TatePointComparison X place parameter) :
    Function.Injective comparison.pointEquiv :=
  comparison.pointEquiv.injective

theorem pointEquiv_surjective
    (comparison : TatePointComparison X place parameter) :
    Function.Surjective comparison.pointEquiv :=
  comparison.pointEquiv.surjective

theorem pointEquiv_map_one
    (comparison : TatePointComparison X place parameter) :
    comparison.pointEquiv (1 : DeckQuotient) = 1 :=
  map_one comparison.pointEquiv

theorem pointEquiv_map_mul
    (comparison : TatePointComparison X place parameter)
    (x y : DeckQuotient) :
    comparison.pointEquiv (x * y) =
      comparison.pointEquiv x * comparison.pointEquiv y :=
  map_mul comparison.pointEquiv x y

theorem pointEquiv_map_inv
    (comparison : TatePointComparison X place parameter)
    (x : DeckQuotient) :
    comparison.pointEquiv x⁻¹ =
      (comparison.pointEquiv x)⁻¹ := by
  simp

theorem galois_naturality_mk
    (comparison : TatePointComparison X place parameter)
    (sigma : AlgebraicClosure (NumberFieldFinitePlace.Completion place)
      ≃ₐ[NumberFieldFinitePlace.Completion place]
      AlgebraicClosure (NumberFieldFinitePlace.Completion place))
    (x : LocalUnit) :
    comparison.pointEquiv (QuotientGroup.mk
      (Units.map sigma.toRingEquiv.toMonoidHom x)) =
      Multiplicative.ofAdd
        ((X.baseChange (NumberFieldFinitePlace.Completion place)).galoisActionOnPoint
          sigma (comparison.pointEquiv (QuotientGroup.mk x)).toAdd) :=
  comparison.galois_naturality sigma x

theorem galois_naturality_quotient
    (comparison : TatePointComparison X place parameter)
    (sigma : AlgebraicClosure (NumberFieldFinitePlace.Completion place)
      ≃ₐ[NumberFieldFinitePlace.Completion place]
      AlgebraicClosure (NumberFieldFinitePlace.Completion place))
    (x : LocalUnit) :
    comparison.pointEquiv
      (NumberFieldFinitePlace.tateDeckQuotientEquiv
        place parameter.q parameter.q_ne_zero sigma
        (QuotientGroup.mk x)) =
      Multiplicative.ofAdd
        ((X.baseChange (NumberFieldFinitePlace.Completion place)).galoisActionOnPoint
          sigma (comparison.pointEquiv (QuotientGroup.mk x)).toAdd) := by
  rw [NumberFieldFinitePlace.tateDeckQuotientEquiv_mk]
  exact comparison.galois_naturality sigma x

end TatePointComparison

structure TateCurveComparison
    {F : Type u} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) where
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion place) parameter.q).IsElliptic
  coordinateChange :
    WeierstrassCurve.VariableChange
      (NumberFieldFinitePlace.Completion place)
  realizesCurve :
    coordinateChange • TateCurve.weierstrassCurve
        (NumberFieldFinitePlace.Completion place) parameter.q =
      (X.baseChange (NumberFieldFinitePlace.Completion place)).curve
  points : TatePointComparison X place parameter

namespace TateCurveComparison

variable {F : Type u} [Field F] [NumberField F]
variable {X : PuncturedEllipticCurve F}
variable {place : NumberField.FinitePlace F}
variable {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}

theorem coordinate_realization
    (comparison : TateCurveComparison X place parameter) :
    comparison.coordinateChange • TateCurve.weierstrassCurve
        (NumberFieldFinitePlace.Completion place) parameter.q =
      (X.baseChange (NumberFieldFinitePlace.Completion place)).curve :=
  comparison.realizesCurve

theorem canonical_elliptic
    (comparison : TateCurveComparison X place parameter) :
    (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion place) parameter.q).IsElliptic :=
  comparison.canonicalIsElliptic

def toUniformization
    (comparison : TateCurveComparison X place parameter) :
    CurveIndexedTateUniformization X place parameter :=
  { canonicalIsElliptic := comparison.canonicalIsElliptic
    coordinateChange := comparison.coordinateChange
    realizesCurve := comparison.realizesCurve
    pointUniformization := comparison.points.pointEquiv
    pointUniformization_galoisEquivariant :=
      comparison.points.galois_naturality }

def point_comparison
    (comparison : TateCurveComparison X place parameter) :
    TatePointComparison X place parameter :=
  comparison.points

theorem toUniformization_coordinate
    (comparison : TateCurveComparison X place parameter) :
    comparison.toUniformization.coordinateChange = comparison.coordinateChange :=
  rfl

theorem toUniformization_curve
    (comparison : TateCurveComparison X place parameter) :
    comparison.toUniformization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q =
      (X.baseChange (NumberFieldFinitePlace.Completion place)).curve :=
  comparison.realizesCurve

theorem toUniformization_points
    (comparison : TateCurveComparison X place parameter) :
    comparison.toUniformization.pointUniformization =
      comparison.points.pointEquiv :=
  rfl

end TateCurveComparison

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tatePointQuotientBoundary : Obligation :=
  { id := "Foundations.Geometry.tate-point-quotient-boundary"
    source := "IUT I, Definition 3.1(c); Tate quotient and point comparison"
    status := VerificationStatus.interface
    note :=
      "The algebraic q^Z quotient and its Galois transport are reused from " ++
        "proved foundations. This module records the separate point comparison " ++
        "and its composition with coordinate data; no analytic comparison is " ++
        "asserted."
    dependsOn :=
      [ "Foundations.Geometry.concrete-tate-deck-quotient",
        "Foundations.Geometry.curve-indexed-tate-uniformization" ] }

end LeanFormal.IUT.Audit
