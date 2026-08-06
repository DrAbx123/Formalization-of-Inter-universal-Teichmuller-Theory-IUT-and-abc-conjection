import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import LeanFormal.IUT.Foundations.Geometry.TateCurve
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
  The exact curve-indexed Tate-uniformization boundary.

  A `FinitePlaceQCandidate` is not promoted to a Tate parameter here.  The
  following structure requires the canonical q-series equation, an actual
  coordinate identification with the selected curve, the quotient-point
  uniformization, and its absolute-Galois equivariance.  No constructor is
  supplied because these are the genuine missing C-layer theorems.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace NumberFieldFinitePlace

/- The adic completion inherits characteristic zero from its number field.
   This is a typeclass bridge only; it adds no mathematical assumption. -/
noncomputable instance completionCharZero
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) :
    CharZero (NumberFieldFinitePlace.Completion place) :=
  Algebra.charZero_of_charZero K
    (NumberFieldFinitePlace.Completion place)

noncomputable def tateParameterUnit
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : Completion place) (q_ne_zero : q ≠ 0) :
    (AlgebraicClosure (Completion place))ˣ :=
    Units.map
      (algebraMap (Completion place)
        (AlgebraicClosure (Completion place))).toMonoidHom
    (Units.mk0 q q_ne_zero)

theorem tateParameterUnit_ne_one
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : Completion place) (q_ne_zero : q ≠ 0) (q_ne_one : q ≠ 1) :
    tateParameterUnit place q q_ne_zero ≠ 1 := by
  intro h
  apply q_ne_one
  apply FaithfulSMul.algebraMap_injective
    (Completion place) (AlgebraicClosure (Completion place))
  have hval := congrArg Units.val h
  simpa [tateParameterUnit] using hval

@[simp] theorem tateParameterUnit_pow
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : Completion place) (q_ne_zero : q ≠ 0) (n : Nat) :
    tateParameterUnit place (q ^ n) (pow_ne_zero n q_ne_zero) =
      (tateParameterUnit place q q_ne_zero) ^ n := by
  apply Units.ext
  simp [tateParameterUnit]

theorem tateParameterUnit_algEquiv_map
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : Completion place) (q_ne_zero : q ≠ 0)
    (sigma : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
      AlgebraicClosure (Completion place)) :
    Units.map sigma.toRingEquiv.toMonoidHom
        (tateParameterUnit place q q_ne_zero) =
      tateParameterUnit place q q_ne_zero := by
  apply Units.ext
  simp [tateParameterUnit]

theorem tateParameterDeckSubgroup_algEquiv_map
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : Completion place) (q_ne_zero : q ≠ 0)
    (sigma : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
      AlgebraicClosure (Completion place)) :
    Subgroup.map (Units.map sigma.toRingEquiv.toMonoidHom)
        (Subgroup.zpowers (tateParameterUnit place q q_ne_zero)) =
      Subgroup.zpowers (tateParameterUnit place q q_ne_zero) := by
  rw [MonoidHom.map_zpowers, tateParameterUnit_algEquiv_map]

end NumberFieldFinitePlace

structure CurveIndexedTateUniformization
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
    coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q =
      (X.baseChange (NumberFieldFinitePlace.Completion place)).curve
  pointUniformization :
    let localCurve := X.baseChange (NumberFieldFinitePlace.Completion place)
    letI : localCurve.curve.IsElliptic := localCurve.isElliptic
    ((AlgebraicClosure (NumberFieldFinitePlace.Completion place))ˣ ⧸
      Subgroup.zpowers
        (NumberFieldFinitePlace.tateParameterUnit
          place parameter.q parameter.q_ne_zero)) ≃*
      Multiplicative localCurve.AlgebraicClosurePoint
  pointUniformization_galoisEquivariant :
    let localCurve := X.baseChange (NumberFieldFinitePlace.Completion place)
    letI : localCurve.curve.IsElliptic := localCurve.isElliptic
    ∀ (sigma :
        AlgebraicClosure (NumberFieldFinitePlace.Completion place) ≃ₐ[
          NumberFieldFinitePlace.Completion place]
        AlgebraicClosure (NumberFieldFinitePlace.Completion place))
      (x : (AlgebraicClosure
        (NumberFieldFinitePlace.Completion place))ˣ),
      pointUniformization
          (QuotientGroup.mk
            (Units.map sigma.toRingEquiv.toMonoidHom x)) =
        Multiplicative.ofAdd
          (localCurve.galoisActionOnPoint sigma
            (pointUniformization (QuotientGroup.mk x)).toAdd)

theorem CurveIndexedTateUniformization.coordinate_realization
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (realization : CurveIndexedTateUniformization X place parameter) :
    realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q =
      (X.baseChange (NumberFieldFinitePlace.Completion place)).curve :=
  realization.realizesCurve

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def curveIndexedTateUniformization : Obligation :=
  { id := "Foundations.Geometry.curve-indexed-tate-uniformization"
    source := "IUT I, Definition 3.1(c); split multiplicative Tate uniformization"
    status := VerificationStatus.interface
    note :=
      "The exact typed contract requires canonical q-series ellipticity, an " ++
        "actual coordinate identification with the selected curve, quotient " ++
        "uniformization, and Galois equivariance. No field is populated by an " ++
        "arbitrary proof; a constructor remains a genuine C-layer obligation."
    dependsOn :=
      [ "Foundations.NumberField.local-q-parameter-valuation",
        "Foundations.Geometry.tate-curve-q-series",
        "Foundations.Geometry.elliptic-torsion-galois" ] }

end LeanFormal.IUT.Audit
